#include "cutils.h"
#include <assert.h>
#include <fenv.h>
#include <inttypes.h>
#include <math.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <time.h>
#if defined(__APPLE__)
#include <malloc/malloc.h>
#elif defined(__linux__)
#include <malloc.h>
#elif defined(__FreeBSD__)
#include <malloc_np.h>
#endif

#include "libbf.h"
#include "libregexp.h"
#include "list.h"
#include "quickjs.h"
#include <fcntl.h>
#include <sched.h>
#include <unistd.h>
#include <x86intrin.h>

#define SHORT_OPCODES 1

typedef enum OPCodeFormat {
#define FMT(f) OP_FMT_##f,
#define DEF(id, size, n_pop, n_push, f)
#include "quickjs-opcode.h"
#undef DEF
#undef FMT
} OPCodeFormat;

enum OPCodeEnum {
#define FMT(f)
#define DEF(id, size, n_pop, n_push, f) OP_##id,
#define def(id, size, n_pop, n_push, f)
#include "quickjs-opcode.h"
#undef def
#undef DEF
#undef FMT
	OP_COUNT, /* excluding temporary opcodes */
	/* temporary opcodes : overlap with the short opcodes */
	OP_TEMP_START = OP_nop + 1,
	OP___dummy = OP_TEMP_START - 1,
#define FMT(f)
#define DEF(id, size, n_pop, n_push, f)
#define def(id, size, n_pop, n_push, f) OP_##id,
#include "quickjs-opcode.h"
#undef def
#undef DEF
#undef FMT
	OP_TEMP_END,
};

typedef struct JSOpCode {
	const char* name;
	uint8_t size; /* in bytes */
	/* the opcodes remove n_pop items from the top of the stack, then
	   pushes n_push items */
	uint8_t n_pop;
	uint8_t n_push;
	uint8_t fmt;
} JSOpCode;

static const JSOpCode opcode_info[OP_COUNT + (OP_TEMP_END - OP_TEMP_START)] = {
#define FMT(f)
#define DEF(id, size, n_pop, n_push, f) {#id, size, n_pop, n_push, OP_FMT_##f},
#define def(id, size, n_pop, n_push, f)
#include "quickjs-opcode.h"
#undef DEF
#undef FMT
};

#define OP_FINAL_COUNT (OP_COUNT + (OP_TEMP_END - OP_TEMP_START))

typedef struct function_object_t {
	const char* func_name;
	uint8_t* bytecode_buf;
	uint32_t bytecode_len;
	uint32_t bytecode_cnt;
	uint32_t v_pc;
} function_object_t;

typedef struct node_t {
	uint32_t pid;  // PC Offset
	uint32_t op;   // OP ID
	const char* opstr;
} node_t;

typedef struct edge_t {
	uint32_t src;
	uint32_t sink;
	uint32_t weight;
	struct edge_t* next;
} edge_t;

typedef struct path_t {
	uint32_t node;
	edge_t* edge;
	struct path_t* r_path;
} path_t;

typedef struct pathlist_t {
	path_t* path;
	struct pathlist_t* r_plist;
} pathlist_t;

typedef struct ts_instance_t {
	int32_t time;
	struct ts_instance_t* next;
} ts_instance_t;

typedef struct ts_series_t {
	ts_instance_t* series[OP_FINAL_COUNT];
	ts_instance_t* series_tail[OP_FINAL_COUNT];
} ts_series_t;

#define MAX_NNODE (1 << 12)
#define MAX_NEDGE (1 << 14)
typedef struct graph_t {
	node_t nodes[MAX_NNODE];
	uint32_t pc_id[MAX_NNODE];
	uint32_t node_cnt;

	uint32_t entry, exit;

	edge_t* node_edges[MAX_NNODE];
	edge_t edges[MAX_NEDGE];
	uint32_t edge_cnt;

	//  tarjan
	uint32_t dfn[MAX_NNODE];
	uint32_t dfn_idx;
	uint32_t dfn_node[MAX_NNODE];
	uint32_t par[MAX_NNODE];
	uint32_t low[MAX_NNODE];
	uint32_t loop_id[MAX_NNODE];
	uint32_t loop_cnt;
	struct graph_t** loops;

	// dominators
	edge_t* sdom_edges[MAX_NNODE];
	edge_t sdom_edge_list[MAX_NEDGE];
	uint32_t sdom_edge_cnt;

	uint32_t djs[MAX_NNODE];
	int32_t djs_val[MAX_NNODE];
	uint32_t sdom[MAX_NNODE];
	uint32_t idom[MAX_NNODE];

	// top-sort
	uint32_t in_degree[MAX_NNODE];
	uint32_t top_order[MAX_NNODE];
	uint32_t top_idx;

	// branching paths
	pathlist_t* br_paths[MAX_NNODE];

	uint32_t OP_dist[MAX_NNODE][OP_FINAL_COUNT];
	struct graph_t* inv_g;

	uint8_t is_loop;
	uint32_t* v_pc;
} graph_t;

graph_t g, inv_g;
int exec_time_given = 0;

#define MAX_NPATH_SQR (1 << 16)
uint32_t diff_set_cnt = 0;
uint8_t* diff_sets[MAX_NPATH_SQR];
uint32_t reduced_op[OP_FINAL_COUNT];

void count_bytecode_instructions(function_object_t* func_obj) {
	uint8_t* base = func_obj->bytecode_buf;
	uint8_t* pc = func_obj->bytecode_buf;
	func_obj->bytecode_cnt = 0;
	for (; pc - base < func_obj->bytecode_len;) {
		++func_obj->bytecode_cnt;
		pc = pc + opcode_info[*pc].size;
	}
	printf("Bytecode Count %u\n", func_obj->bytecode_cnt);
}

function_object_t* load_func_bytecode(const char* func) {
	char filepath[256] = {};
	FILE* file = NULL;
	memcpy(filepath, func, strlen(func));
	file = fopen(filepath, "rb");
	if (file == NULL) {
		sprintf(filepath, ".bytecode/%s", func);
		file = fopen(filepath, "rb");
	}
	if (file == NULL) {
		printf("bytecode file not found");
		return NULL;
	}
	fseek(file, 0, SEEK_END);
	uint32_t bytecode_len = ftell(file);
	rewind(file);
	uint8_t* bytecode_buf = malloc(bytecode_len);
	fread(bytecode_buf, 1, bytecode_len, file);
	fclose(file);

	printf("Read %u bytes from %s:\n", bytecode_len, filepath);
	for (int i = 0; i < bytecode_len; ++i) {
		printf("%02X ", bytecode_buf[i]);
	}
	printf("\n");

	function_object_t* obj = malloc(sizeof(function_object_t));
	obj->func_name = func;
	obj->bytecode_buf = bytecode_buf;
	obj->bytecode_len = bytecode_len;
	obj->v_pc = bytecode_len;
	count_bytecode_instructions(obj);
	return obj;
}

void dump_graph_to_json(graph_t* g, const char* filename) {
	char filepath[256];
	const char* dot = strrchr(filename, '.');

	size_t len = dot - filename;
	/* printf("%.*s\n", (int)len, filename); */
	sprintf(filepath, "%.*s.json", (int)len, filename);
	printf("dump graph to %s\n", filepath);
	FILE* f = fopen(filepath, "w");
	if (!f) {
		perror("fopen");
		return;
	}

	fprintf(f, "{\n  \"nodes\": [\n");
	for (uint32_t i = 0; i < g->node_cnt; ++i) {
		fprintf(f, "    {\"id\": \"%u\", \"label\": \"%d:%s\"}%s\n", i,
				g->nodes[i].pid, g->nodes[i].opstr,
				(i == g->node_cnt - 1) ? "" : ",");
	}
	fprintf(f, "  ],\n  \"links\": [\n");

	int first = 1;
	for (int i = 0; i < g->edge_cnt; ++i) {
		edge_t* e = &g->edges[i];
		if (!first)
			fprintf(f, ",\n");
		fprintf(f,
				"    {\"source\": \"%u\", \"target\": \"%u\", \"label\": %d}",
				e->src, e->sink, e->weight);
		first = 0;
	}

	fprintf(f, "\n  ]\n}\n");
	fclose(f);
}

void insert_sdom_edge(graph_t* g,
					  uint32_t src_id,
					  uint32_t sink_id,
					  uint32_t weight) {
	g->sdom_edge_list[g->sdom_edge_cnt] =
		(edge_t){.src = src_id,
				 .sink = sink_id,
				 .weight = weight,
				 .next = g->sdom_edges[src_id]};
	g->sdom_edges[src_id] = &g->sdom_edge_list[g->sdom_edge_cnt++];
}

void insert_node(graph_t* g, node_t node) {
	if (g->pc_id[node.pid] != -1) {
		return;
	}
	g->pc_id[node.pid] = g->node_cnt;
	g->nodes[g->node_cnt].pid = node.pid;
	g->nodes[g->node_cnt].op = node.op;
	g->nodes[g->node_cnt].opstr = node.opstr;
	++g->node_cnt;
}

void insert_node_inst(graph_t* g,
					  uint32_t pid,
					  uint32_t op,
					  const char* opstr) {
	uint32_t nid;
	if (g->pc_id[pid] == -1) {
		g->pc_id[pid] = g->node_cnt++;
	}
	nid = g->pc_id[pid];
	g->nodes[nid].pid = pid;
	/* g->nodes[nid].op = op; */
	// PROG
	g->nodes[nid].op = reduced_op[op];
	g->nodes[nid].opstr = opstr;
}

void insert_edge(graph_t* g,
				 uint32_t src_id,
				 uint32_t sink_id,
				 uint32_t weight) {
	assert(src_id != -1);
	assert(sink_id != -1);
	g->edges[g->edge_cnt] = (edge_t){.src = src_id,
									 .sink = sink_id,
									 .weight = weight,
									 .next = g->node_edges[src_id]};
	g->node_edges[src_id] = &g->edges[g->edge_cnt++];
}

void insert_edge_by_pid(graph_t* g,
						uint32_t src_pid,
						uint32_t sink_pid,
						uint32_t weight) {
	insert_edge(g, g->pc_id[src_pid], g->pc_id[sink_pid], weight);
}

void init_graph(graph_t* g) {
	memset(g, 0, sizeof(graph_t));
	memset(g->pc_id, -1, sizeof(g->pc_id));
	memset(g->par, -1, sizeof(g->par));
	memset(g->dfn, -1, sizeof(g->dfn));
	memset(g->low, -1, sizeof(g->low));
	memset(g->loop_id, -1, sizeof(g->loop_id));
	memset(g->OP_dist, 0xff, sizeof(g->OP_dist));
	g->inv_g = malloc(sizeof(graph_t));
}

void init_inv_graph(graph_t* g) {
	memset(g, 0, sizeof(graph_t));
	memset(g->pc_id, -1, sizeof(g->pc_id));
	memset(g->par, -1, sizeof(g->par));
	memset(g->dfn, -1, sizeof(g->dfn));
	memset(g->low, -1, sizeof(g->low));
	memset(g->loop_id, -1, sizeof(g->loop_id));
	memset(g->OP_dist, 0xff, sizeof(g->OP_dist));
}

void inverse_graph(graph_t* g) {
	graph_t* inv_g = g->inv_g;
	init_inv_graph(inv_g);
	inv_g->inv_g = g;
	memcpy(inv_g->nodes, g->nodes, sizeof(g->nodes));
	inv_g->node_cnt = g->node_cnt;
	inv_g->entry = g->exit;
	inv_g->exit = g->entry;
	for (int i = 0; i < g->edge_cnt; ++i) {
		edge_t* edge = &g->edges[i];
		insert_edge(inv_g, edge->sink, edge->src, edge->weight);
	}
}

void reduce_ops() {
	for (int i = 0; i < OP_FINAL_COUNT; ++i) {
		reduced_op[i] = i;
	}

	typedef struct {
		enum OPCodeEnum origin;
		enum OPCodeEnum reduced;
	} op_reduce_pair_t;
	op_reduce_pair_t reduce_pairs[] = {
		{OP_push_0, OP_push_0},      {OP_push_1, OP_push_0},
		{OP_push_2, OP_push_0},      {OP_push_3, OP_push_0},
		{OP_push_4, OP_push_0},      {OP_push_5, OP_push_0},
		{OP_push_6, OP_push_0},      {OP_push_7, OP_push_0},
		{OP_goto8, OP_goto},         {OP_goto16, OP_goto},
		{OP_if_false8, OP_if_false}, {OP_if_true8, OP_if_true}};

	int pair_count = sizeof(reduce_pairs) / sizeof(reduce_pairs[0]);

	for (int i = 0; i < pair_count; i++) {
		op_reduce_pair_t rp = reduce_pairs[i];
		reduced_op[rp.origin] = rp.reduced;
	}
}

void parse_bytecodes(function_object_t* func_obj, uint32_t* exec_time) {
	uint8_t* base = func_obj->bytecode_buf;
	uint8_t *pc = func_obj->bytecode_buf, *next_pc;
	int32_t jump_offset;
	uint32_t pid;
	node_t* node;
	uint32_t sink;

	reduce_ops();
	init_graph(&g);
	init_graph(&inv_g);
	for (; pc - base < func_obj->bytecode_len;) {
		pid = pc - base;
		insert_node_inst(&g, pid, *pc, opcode_info[*pc].name);

		if (exec_time_given && exec_time[pid] == 0) {
			printf("Warn: Execution time of [%d:%s] is unknown\n", pid,
				   opcode_info[*pc].name);
		}
		switch (*pc) {
			case OP_goto:
			case OP_goto16:
			case OP_goto8:
				switch (*pc) {
					case OP_goto:
						jump_offset = (int32_t)get_u32(pc + 1);
						break;
					case OP_goto16:
						jump_offset = (int16_t)get_u16(pc + 1);
						break;
					case OP_goto8:
						jump_offset = (int8_t)*(pc + 1);
						break;
				}
				printf("[%04u:%02X]: %s offset: %d, target %u\n", pid, *pc,
					   opcode_info[*pc].name, jump_offset,
					   pid + jump_offset + 1);

				sink = pid + jump_offset + 1;
				if (g.pc_id[sink] == -1) {
					g.pc_id[sink] = g.node_cnt++;
				}
				// FIXME: exec time of goto
				insert_edge(&g, g.pc_id[pid], g.pc_id[sink], 100);
				/* insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]); */

				next_pc = pc + opcode_info[*pc].size;
				break;
			case OP_if_false:
			case OP_if_true:
				jump_offset = (int32_t)get_u32(pc + 1);
				printf("[%04u:%02X]: %s offset: %d, target %u\n", pid, *pc,
					   opcode_info[*pc].name, jump_offset,
					   pid + jump_offset + 1);

				sink = pid + opcode_info[*pc].size;
				if (g.pc_id[sink] == -1) {
					g.pc_id[sink] = g.node_cnt++;
				}
				// FIXME: exec time of if_
				insert_edge(&g, g.pc_id[pid], g.pc_id[sink], 100);
				/* insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]); */

				sink = pid + jump_offset + 1;
				if (g.pc_id[sink] == -1) {
					g.pc_id[sink] = g.node_cnt++;
				}
				// FIXME: exec time of if_
				insert_edge(&g, g.pc_id[pid], g.pc_id[sink], 100);
				/* insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]); */

				next_pc = pc + opcode_info[*pc].size;
				break;
			case OP_if_true8:
			case OP_if_false8:
				jump_offset = (int8_t)*(pc + 1);
				printf("[%04u:%02X]: %s offset: %d, target %u\n", pid, *pc,
					   opcode_info[*pc].name, jump_offset,
					   pid + jump_offset + 1);

				sink = pid + opcode_info[*pc].size;
				if (g.pc_id[sink] == -1) {
					g.pc_id[sink] = g.node_cnt++;
				}
				// FIXME: exec time of if_
				insert_edge(&g, g.pc_id[pid], g.pc_id[sink], 100);
				/* insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]); */

				sink = pid + jump_offset + 1;
				if (g.pc_id[sink] == -1) {
					g.pc_id[sink] = g.node_cnt++;
				}
				// FIXME: exec time of if_
				insert_edge(&g, g.pc_id[pid], g.pc_id[sink], 100);
				/* insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]); */

				next_pc = pc + opcode_info[*pc].size;
				break;
			default:
				printf("[%04u:%02X]: %s += %d\n", pid, *pc,
					   opcode_info[*pc].name, opcode_info[*pc].size);

				sink = pid + opcode_info[*pc].size;
				if (g.pc_id[sink] == -1) {
					g.pc_id[sink] = g.node_cnt++;
				}
				insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]);

				next_pc = pc + opcode_info[*pc].size;
				break;
		}
		pc = next_pc;
	}
	pid = pc - base;
	node = &g.nodes[g.pc_id[pid]];
	node->pid = pid;
	node->opstr = "VIRT_EXIT";
	g.entry = g.pc_id[0];
	g.exit = g.pc_id[pid];
	g.v_pc = &func_obj->v_pc;
	inverse_graph(&g);

	dump_graph_to_json(&g, func_obj->func_name);
	return;
}

uint32_t* load_exec_time(const function_object_t* func_obj,
						 const char* profile_file) {
	char filepath[256];
	FILE* file = NULL;
	file = fopen(profile_file, "rb");
	if (file == NULL) {
		sprintf(filepath, "%s.perf", profile_file);
		file = fopen(filepath, "rb");
	}
	if (file == NULL) {
		printf("Profile file not found");
		return NULL;
	}
	int32_t id;
	char opstr[32];
	double mean, cv;
	uint32_t* exec_time = malloc(sizeof(uint32_t) * func_obj->bytecode_len);
	while (fscanf(file, "%d %s %lf %lf", &id, opstr, &mean, &cv) == 4) {
		exec_time[id] = (uint32_t)mean;
	}
	fclose(file);
	return exec_time;
}

void dfs_graph(graph_t* g, uint32_t u) {
	g->dfn[u] = g->low[u] = g->dfn_idx;

	g->dfn_node[g->dfn_idx] = u;
	++g->dfn_idx;
	for (edge_t* edge = g->node_edges[u]; edge != NULL; edge = edge->next) {
		uint32_t v = edge->sink;
		if (g->dfn[v] == -1) {
			g->par[v] = u;
			dfs_graph(g, v);
		}
		g->low[u] = g->low[u] < g->low[v] ? g->low[u] : g->low[v];
	}
}

int graph_dfn_comp(const void* a, const void* b, void* ctx) {
	graph_t* g = (graph_t*)ctx;
	int u = *(const int*)a;
	int v = *(const int*)b;
	return g->dfn[u] - g->dfn[v];
}

int djs_find(graph_t* g, uint32_t u) {
	if (g->djs[u] == u) {
		return u;
	}

	uint32_t v = djs_find(g, g->djs[u]);
	g->djs[u] = v;
	if (g->dfn[g->djs_val[u]] < g->dfn[g->djs_val[v]]) {
		g->djs_val[v] = g->djs_val[u];
	}
	return g->djs[u];
}

void lengauer(graph_t* g) {
	graph_t* inv_g = g->inv_g;
	dfs_graph(inv_g, inv_g->entry);
	for (int i = 0; i < inv_g->node_cnt; ++i) {
		inv_g->djs[i] = inv_g->djs_val[i] = inv_g->sdom[i] = i;
	}
	for (int i = inv_g->dfn_idx - 1; i > 0; --i) {
		uint32_t u = inv_g->dfn_node[i];
		for (edge_t* edge = g->node_edges[u]; edge != NULL; edge = edge->next) {
			uint32_t v = edge->sink;

			if (inv_g->dfn[v] < inv_g->dfn[u]) {
				if (inv_g->dfn[v] < inv_g->dfn[inv_g->sdom[u]]) {
					inv_g->sdom[u] = v;
				}

			} else {
				uint32_t djs_v = djs_find(inv_g, v);
				uint32_t sdom = inv_g->sdom[u], sdom_c = inv_g->djs_val[djs_v];
				if (inv_g->dfn[sdom_c] < inv_g->dfn[sdom]) {
					inv_g->sdom[u] = sdom_c;
				}
			}
		}

		inv_g->djs_val[u] = inv_g->sdom[u];
		inv_g->djs[u] = inv_g->par[u];

		/* printf("sdom %d: %d\n", g->nodes[u].pid, g->nodes[g->sdom[u]].pid); */

		insert_sdom_edge(inv_g, inv_g->sdom[u], u, 0);
		for (edge_t* edge = inv_g->sdom_edges[inv_g->par[u]]; edge != NULL;
			 edge = edge->next) {
			uint32_t v = edge->sink, djs_v = djs_find(inv_g, v);
			if (inv_g->dfn[inv_g->sdom[djs_v]] < inv_g->dfn[inv_g->sdom[v]]) {
				inv_g->idom[v] = djs_v;
			} else {
				inv_g->idom[v] = inv_g->par[u];
			}
			--inv_g->sdom_edge_cnt;
		}
		inv_g->sdom_edges[inv_g->par[u]] = NULL;
	}

	for (int i = 1; i < inv_g->dfn_idx; ++i) {
		uint32_t u = inv_g->dfn_node[i];

		if (inv_g->idom[u] != inv_g->sdom[u]) {
			inv_g->idom[u] = inv_g->idom[inv_g->idom[u]];
		}

		/* printf("idom[%d]: %d\n", g->nodes[u].pid, g->nodes[g->idom[u]].pid); */
	}
}

void top_sort_graph_with_OP_distance(graph_t* g) {
	uint32_t queue[MAX_NNODE];
	uint32_t front = 0, back = 0;

	for (uint32_t i = 0; i < g->edge_cnt; ++i) {
		edge_t* e = &g->edges[i];
		++g->in_degree[e->sink];
	}

	for (uint32_t u = 0; u < g->node_cnt; ++u) {
		if (g->in_degree[u] == 0) {
			queue[back++] = u;
		}
	}
	g->top_idx = 0;
	while (front < back) {
		uint32_t u = queue[front++], op = g->nodes[u].op;
		g->top_order[g->top_idx++] = u;
		g->OP_dist[u][op] = 0;
		for (edge_t* e = g->node_edges[u]; e != NULL; e = e->next) {
			uint32_t v = e->sink;
			if (--g->in_degree[v] == 0) {
				queue[back++] = v;
			}

			for (int j = 1; j < OP_FINAL_COUNT; ++j) {
				if (g->OP_dist[u][j] != UINT32_MAX &&
					g->OP_dist[v][j] > g->OP_dist[u][j] + e->weight) {
					g->OP_dist[v][j] = g->OP_dist[u][j] + e->weight;
				}
			}
		}
	}

	/* for (int i = 0; i < g->top_idx; ++i) { */
	/*     printf("top[%d]: %d\n", i, g->nodes[i].pid); */
	/*     for (int j = 1; j < OP_FINAL_COUNT; ++j) { */
	/*         if (g->OP_dist[i][j] != UINT32_MAX) { */
	/*             printf("node [%d:%s]--[%d:%s] dist: %d\n", i, g->nodes[i].opstr, */
	/*                    j, opcode_info[j].name, g->OP_dist[i][j]); */
	/*         } */
	/*     } */
	/* } */
	if (g->top_idx < g->node_cnt) {
		printf("Error: Graph has cycles.\n");
		exit(1);
	}
}

void solve_loop_OP_distance(graph_t* g) {
	uint32_t queue[MAX_NNODE], inqueue[MAX_NNODE] = {};
	uint32_t front = 0, back = 0;

	queue[back++] = g->entry;
	inqueue[g->entry] = 1;
	while (front < back) {
		uint32_t u = queue[front++], op = g->nodes[u].op;
		g->OP_dist[u][op] = 0;
		for (edge_t* e = g->node_edges[u]; e != NULL; e = e->next) {
			uint32_t v = e->sink;
			for (int j = 1; j < OP_FINAL_COUNT; ++j) {
				if (g->OP_dist[u][j] != UINT32_MAX &&
					g->OP_dist[v][j] > g->OP_dist[u][j] + e->weight) {
					g->OP_dist[v][j] = g->OP_dist[u][j] + e->weight;
					if (!inqueue[v]) {
						queue[back++] = v;
						inqueue[v] = 1;
					}
				}
			}
		}
	}

	/* for (int i = 0; i < g->top_idx; ++i) { */
	/*     for (int j = 1; j < OP_FINAL_COUNT; ++j) { */
	/*         if (g->OP_dist[i][j] != UINT32_MAX) { */
	/*             printf("node [%d:%s]--[%d:%s] dist: %d\n", i, g->nodes[i].opstr, */
	/*                    j, opcode_info[j].name, g->OP_dist[i][j]); */
	/*         } */
	/*     } */
	/* } */
}

ts_series_t* parse_cf_path(graph_t* g, path_t* path) {
	ts_series_t* ts_seris = malloc(sizeof(ts_series_t));
	ts_instance_t* ts_inst;
	uint32_t dist = 0;
	uint32_t u = 0;
	edge_t* e = NULL;

	u = path->node;

	memset(ts_seris, 0, sizeof(ts_series_t));
	for (int i = 1; i < OP_FINAL_COUNT; ++i) {
		if (g->OP_dist[u][i] != UINT32_MAX) {
			ts_inst = malloc(sizeof(ts_instance_t));
			ts_inst->time = -g->OP_dist[u][i];
			ts_inst->next = NULL;
			ts_seris->series[i] = ts_inst;
			ts_seris->series_tail[i] = ts_inst;
		}
	}
	for (; path != NULL; path = path->r_path) {
		u = path->node;
		e = path->edge;

		ts_inst = malloc(sizeof(ts_instance_t));
		ts_inst->time = dist;
		ts_inst->next = NULL;

		if (!ts_seris->series[g->nodes[u].op]) {
			ts_seris->series[g->nodes[u].op] = ts_inst;
		} else {
			ts_seris->series_tail[g->nodes[u].op]->next = ts_inst;
		}
		ts_seris->series_tail[g->nodes[u].op] = ts_inst;
		if (e) {
			dist += e->weight;
		}
	}
	for (int i = 1; i < OP_FINAL_COUNT; ++i) {
		if (g->inv_g->OP_dist[u][i] != UINT32_MAX) {
			dist += g->inv_g->OP_dist[u][i];
			ts_inst = malloc(sizeof(ts_instance_t));
			ts_inst->time = dist;
			ts_inst->next = NULL;

			if (!ts_seris->series[i]) {
				ts_seris->series[i] = ts_inst;
			} else {
				ts_seris->series_tail[i]->next = ts_inst;
			}
			ts_seris->series_tail[i] = ts_inst;
		}
	}
	return ts_seris;
}

#define TIME_WINDOW (2000)
int8_t compare_ts_series(volatile uint32_t op,
						 ts_instance_t* ts_a,
						 ts_instance_t* ts_b) {
	if (ts_a == NULL && ts_b == NULL) {
		return 0;
	} else if (ts_a == NULL) {
		return 1;
	} else if (ts_b == NULL) {
		return 1;
	}
	uint32_t f[MAX_NNODE] = {};
	int32_t time[MAX_NNODE] = {};
	uint8_t ts_c[MAX_NNODE] = {};
	uint32_t f_cnt = 0;
	f[0] = f_cnt = 1;
	time[0] = 0;
	ts_instance_t* proc = NULL;
	uint32_t idx = 0;
	while (ts_a != NULL || ts_b != NULL) {
		++idx;
		if (ts_a == NULL) {
			proc = ts_b;
			ts_c[idx] = 2;
			ts_b = ts_b->next;
		} else if (ts_b == NULL) {
			proc = ts_a;
			ts_c[idx] = 1;
			ts_a = ts_a->next;
		} else {
			if (ts_a->time < ts_b->time) {
				proc = ts_a;
				ts_c[idx] = 1;
				ts_a = ts_a->next;
			} else {
				proc = ts_b;
				ts_c[idx] = 2;
				ts_b = ts_b->next;
			}
		}
		time[idx] = proc->time;
		uint32_t c_a = 0, c_b = 0;
		// TODO: optimization
		for (int i = idx; i > 0 && f[idx] == 0; --i) {
			if (i != 0 && time[idx] - time[i] > TIME_WINDOW) {
				break;
			}
			if (ts_c[i] == 1) {
				++c_a;
			} else if (ts_c[i] == 2) {
				++c_b;
			}
			if (c_a && c_b) {
				f[idx] += f[i - 1];
			}
		}
	}
	return f[idx] == 0;
}

uint8_t* compare_paths(graph_t* g, path_t* pa, path_t* pb) {
	ts_series_t* ts_a = parse_cf_path(g, pa);
	ts_series_t* ts_b = parse_cf_path(g, pb);

	/* for (int i = 1; i < OP_FINAL_COUNT; ++i) { */
	/*     if (ts_a->series[i] != NULL) { */
	/*         printf("OP[%s]: ", opcode_info[i].name); */
	/*         for (ts_instance_t* ts_inst = ts_a->series[i]; ts_inst != NULL; */
	/*              ts_inst = ts_inst->next) { */
	/*             printf("%d -> ", ts_inst->time); */
	/*         } */
	/*         printf("\n"); */
	/*     } */
	/* } */
	uint8_t* diff_set = malloc(sizeof(uint8_t) * OP_FINAL_COUNT);
	for (int i = 1; i < OP_FINAL_COUNT; ++i) {
		diff_set[i] = compare_ts_series(i, ts_a->series[i], ts_b->series[i]);
		/* if (diff_set[i]) { */
		/*	printf("%d:%s differ\n", i, opcode_info[i].name); */
		/* } */
	}
	// TODO free ts_series
	return diff_set;
}

pathlist_t* branching_subgraph_paths(graph_t* g, uint32_t u, uint32_t sink) {
	if (g->br_paths[u] != NULL) {
		return g->br_paths[u];
	}

	pathlist_t* u_plist = NULL;
	path_t *u_path = NULL, *v_path = NULL;
	if (u == sink) {
		u_path = malloc(sizeof(path_t));
		*u_path = (path_t){.node = u, .edge = NULL, .r_path = NULL};

		u_plist = malloc(sizeof(pathlist_t));
		*u_plist = (pathlist_t){.path = u_path, .r_plist = g->br_paths[u]};
		g->br_paths[u] = u_plist;

		return g->br_paths[u];
	}

	for (edge_t* e = g->node_edges[u]; e != NULL; e = e->next) {
		pathlist_t* v_plist = branching_subgraph_paths(g, e->sink, sink);

		while (v_plist != NULL) {
			v_path = v_plist->path;

			u_path = malloc(sizeof(path_t));
			*u_path = (path_t){.node = u, .edge = e, .r_path = v_path};

			u_plist = malloc(sizeof(pathlist_t));
			*u_plist = (pathlist_t){.path = u_path, .r_plist = g->br_paths[u]};
			g->br_paths[u] = u_plist;

			v_plist = v_plist->r_plist;
		}
	}
	return g->br_paths[u];
}

void print_path(graph_t* g, path_t* path) {
	uint32_t u = path->edge->src, dist = 0;
	printf("Path: src=");
	for (; path != NULL; path = path->r_path) {
		u = path->node;
		printf("[%d:%s](%d)%s", g->nodes[u].pid, g->nodes[u].opstr, dist,
			   path->edge == NULL ? "" : "->");
		dist += path->edge ? path->edge->weight : 0;
	}
	printf("=sink;\n");
}

void analyze_branching_subgraph(graph_t* g) {
	lengauer(g);

	top_sort_graph_with_OP_distance(g);
	top_sort_graph_with_OP_distance(g->inv_g);

	for (int i = g->top_idx - 1; i >= 0; --i) {
		const char* opstr = g->nodes[g->top_order[i]].opstr;
		if (strncmp(opstr, "if_", strlen("if_")) == 0) {
			uint32_t u = g->top_order[i];
			pathlist_t* plist =
				branching_subgraph_paths(g, u, g->inv_g->idom[u]);
			for (pathlist_t* p = plist; p != NULL; p = p->r_plist) {
				print_path(g, p->path);
			}
			for (pathlist_t* p1 = plist; p1 != NULL; p1 = p1->r_plist) {
				for (pathlist_t* p2 = p1->r_plist; p2 != NULL;
					 p2 = p2->r_plist) {
					diff_sets[diff_set_cnt++] =
						compare_paths(g, p1->path, p2->path);
				}
			}
		}
	}
	if (g->is_loop) {
		insert_edge(g, g->entry, g->exit, 0);
		solve_loop_OP_distance(g);
		graph_t* inv_g = g->inv_g;
		insert_edge(inv_g, inv_g->entry, inv_g->exit, 0);
		solve_loop_OP_distance(inv_g);
	}
}

void parse_graph_loops(graph_t* g) {
	dfs_graph(g, g->entry);
	g->loop_cnt = 0;
	uint32_t scc_size[MAX_NNODE] = {};
	for (uint32_t i = 0; i < g->node_cnt; ++i) {
		/* printf("node %d [%d:%s], low %d, low_pc %d\n", i, g->nodes[i].op, */
		/*	   g->nodes[i].opstr, g->low[i], g->nodes[g->low[i]].op); */
		++scc_size[g->low[i]];
	}
	for (uint32_t i = 0; i < g->node_cnt; ++i) {
		if (g->dfn[i] == g->low[i] && scc_size[g->low[i]] > 1) {
			g->loop_id[g->low[i]] = g->loop_cnt++;
		}
	}
	printf("Loop Count: %d\n", g->loop_cnt);
	g->loops = (graph_t**)malloc(sizeof(graph_t*) * g->loop_cnt);
	for (int i = 0; i < g->loop_cnt; ++i) {
		g->loops[i] = (graph_t*)malloc(sizeof(graph_t));
		init_graph(g->loops[i]);
		g->is_loop = g->inv_g->is_loop = 1;
		g->loops[i]->v_pc = g->v_pc;
	}
	for (uint32_t i = 0; i < g->node_cnt; ++i) {
		uint32_t loop_u = g->loop_id[g->low[i]];
		if (loop_u != -1) {
			insert_node(g->loops[loop_u], g->nodes[i]);
			if (g->dfn[i] == g->low[i]) {
				g->loops[loop_u]->entry = i;
				g->loops[loop_u]->exit = -1;
			}
		}
	}
	for (uint32_t i = 0; i < g->edge_cnt; ++i) {
		uint32_t u, v;
		uint32_t loop_u, loop_v;
		u = g->edges[i].src;
		v = g->edges[i].sink;
		loop_u = g->loop_id[g->low[u]];
		loop_v = g->loop_id[g->low[v]];
		if (loop_u == loop_v && loop_u != -1) {
			if (v == g->loops[loop_u]->entry) {
				if (g->loops[loop_u]->exit == -1) {
					uint32_t* v_pc = g->loops[loop_u]->v_pc;
					++(*v_pc);
					insert_node_inst(g, *v_pc, 0, "VIRT_LOOP_EXIT");
					g->edges[i].sink = g->pc_id[*v_pc];

					insert_node_inst(g->loops[loop_u], *v_pc, 0,
									 "VIRT_LOOP_EXIT");
					insert_edge_by_pid(g->loops[loop_u], g->nodes[u].pid, *v_pc,
									   g->edges[i].weight);
					g->loops[loop_u]->exit = g->loops[loop_u]->pc_id[*v_pc];
				} else {
					uint32_t exid = g->loops[loop_u]->exit;
					g->edges[i].sink = exid;
					insert_edge_by_pid(g->loops[loop_u], g->nodes[u].pid, exid,
									   g->edges[i].weight);
				}
			} else {
				insert_edge_by_pid(g->loops[loop_u], g->nodes[u].pid,
								   g->nodes[v].pid, g->edges[i].weight);
			}
		}
	}
}

uint8_t* pick_op_diff_set() {
	uint8_t* op_set = (uint8_t*)malloc(OP_FINAL_COUNT * sizeof(uint8_t));
	uint8_t* covers = (uint8_t*)malloc(diff_set_cnt * sizeof(uint8_t));

	int32_t opt_op, opt_gain;
	uint32_t diff_remain = diff_set_cnt;
	printf("diff cnt: %d\n", diff_set_cnt);

	memset(op_set, 0, OP_FINAL_COUNT * sizeof(uint8_t));
	memset(covers, 0, diff_set_cnt * sizeof(uint8_t));

	for (; diff_remain > 0;) {
		opt_op = -1;
		opt_gain = 0;

		for (int j = 0; j < OP_FINAL_COUNT; ++j) {
			if (op_set[j])
				continue;

			uint32_t gain = 0;
			for (int p = 0; p < diff_set_cnt; ++p) {
				if (!covers[p] && diff_sets[p][j]) {
					gain++;
				}
			}

			if (gain > opt_gain) {
				opt_gain = gain;
				opt_op = j;
			}
		}
		if (opt_op == -1) {
			break;
		}
		op_set[opt_op] = 1;

		for (int p = 0; p < diff_set_cnt; ++p) {
			if (!covers[p] && diff_sets[p][opt_op]) {
				covers[p] = 1;
				--diff_remain;
			}
		}
	}

	printf("\nOP Selection\n");
	for (int i = 0; i < OP_FINAL_COUNT; ++i) {
		if (op_set[i]) {
			printf("op [%d:%s]\n", i, opcode_info[i].name);
		}
	}
	printf("\n\n");
	return op_set;
}

void sc_analyze(const char* filename, const char* profile_file) {
	function_object_t* func_obj = load_func_bytecode(filename);
	uint32_t* exec_time = NULL;
	if (profile_file) {
		exec_time_given = 1;
		exec_time = load_exec_time(func_obj, profile_file);
	} else {
		printf("Warn: Execution time is unknown\n");
		exec_time = malloc(sizeof(uint32_t) * func_obj->bytecode_len);
		memset(exec_time, 0, sizeof(uint32_t) * func_obj->bytecode_len);
	}
	parse_bytecodes(func_obj, exec_time);
	parse_graph_loops(&g);
	for (int i = 0; i < g.loop_cnt; ++i) {
		char dump_name[128];
		sprintf(dump_name, "loopi_%d", i);
		dump_graph_to_json(g.loops[i], dump_name);
		inverse_graph(g.loops[i]);
		analyze_branching_subgraph(g.loops[i]);
		pick_op_diff_set();
	}
	analyze_branching_subgraph(&g);
	pick_op_diff_set();
}

int main(int argc, char** argv) {
	if (argc <= 1) {
		printf("function name not provided\n");
		return 1;
	} else if (argc <= 2) {
		sc_analyze(argv[1], NULL);
	} else {
		sc_analyze(argv[1], argv[2]);
	}
	return 0;
}
