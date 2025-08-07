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
} function_object_t;

int exec_time_given = 0;

function_object_t* load_func_bytecode(const char* func) {
    char filepath[256];
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
    return obj;
}

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

    // dominators
    edge_t* sdom_edges[MAX_NNODE];
    edge_t sdom_edge_list[MAX_NEDGE];
    uint32_t sdom_edge_cnt;

    uint32_t dfn[MAX_NNODE];
    uint32_t dfn_idx;
    uint32_t dfn_node[MAX_NNODE];
    uint32_t par[MAX_NNODE];
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
} graph_t;

graph_t g, inv_g;

void dump_graph_to_json(graph_t* g, const char* filename) {
    char filepath[256];
    const char* dot = strrchr(filename, '.');

    size_t len = dot - filename;
    printf("%.*s\n", (int)len, filename);
    sprintf(filepath, "%.*s.json", (int)len, filename);
    printf("write to %s\n", filepath);
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

void insert_edge(graph_t* g,
                 uint32_t src_id,
                 uint32_t sink_id,
                 uint32_t weight) {
    g->edges[g->edge_cnt] = (edge_t){.src = src_id,
                                     .sink = sink_id,
                                     .weight = weight,
                                     .next = g->node_edges[src_id]};
    g->node_edges[src_id] = &g->edges[g->edge_cnt++];
}

void init_graph(graph_t* g) {
    memset(g, 0, sizeof(graph_t));
    memset(g->pc_id, -1, sizeof(g->pc_id));
    memset(g->par, -1, sizeof(g->par));
    memset(g->dfn, -1, sizeof(g->dfn));
}

void inverse_graph(graph_t* g, graph_t* inv_g) {
    init_graph(inv_g);
    memcpy(inv_g->nodes, g->nodes, sizeof(g->nodes));
    g->inv_g = inv_g;
    inv_g->inv_g = g;
    inv_g->node_cnt = g->node_cnt;
    inv_g->entry = g->exit;
    inv_g->exit = g->entry;
    for (int i = 0; i < g->edge_cnt; ++i) {
        edge_t* edge = &g->edges[i];
        insert_edge(inv_g, edge->sink, edge->src, edge->weight);
    }
}

void parse_bytecodes(function_object_t* func_obj, uint32_t* exec_time) {
    uint8_t* base = func_obj->bytecode_buf;
    uint8_t *pc = func_obj->bytecode_buf, *next_pc;
    uint32_t inst_cnt = 0;
    int32_t jump_offset;
    uint32_t pid;
    node_t* node;
    uint32_t sink;

    init_graph(&g);
    init_graph(&inv_g);
    for (; pc - base < func_obj->bytecode_len;) {
        pid = pc - base;
        ++inst_cnt;
        if (g.pc_id[pid] == -1) {
            g.pc_id[pid] = g.node_cnt++;
        }
        node = &g.nodes[g.pc_id[pid]];
        node->pid = pid;
        node->op = *pc;
        node->opstr = opcode_info[*pc].name;

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
                        jump_offset = (int32_t)*(pc + 1);
                        break;
                    case OP_goto16:
                        jump_offset = (int16_t)*(pc + 1);
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
                insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]);
                next_pc = pc + opcode_info[*pc].size;
                break;
            case OP_if_false:
            case OP_if_true:
                jump_offset = (int32_t)*(pc + 1);
                printf("[%04u:%02X]: %s offset: %d, target %u\n", pid, *pc,
                       opcode_info[*pc].name, jump_offset,
                       pid + jump_offset + 1);

                sink = pid + opcode_info[*pc].size;
                if (g.pc_id[sink] == -1) {
                    g.pc_id[sink] = g.node_cnt++;
                }
                insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]);

                sink = pid + jump_offset + 1;
                if (g.pc_id[sink] == -1) {
                    g.pc_id[sink] = g.node_cnt++;
                }
                insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]);

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
                insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]);

                sink = pid + jump_offset + 1;
                if (g.pc_id[sink] == -1) {
                    g.pc_id[sink] = g.node_cnt++;
                }
                insert_edge(&g, g.pc_id[pid], g.pc_id[sink], exec_time[pid]);

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
    printf("Total instructions: %d\n", inst_cnt);
    inverse_graph(&g, &inv_g);

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
    g->dfn[u] = g->dfn_idx;
    g->dfn_node[g->dfn_idx] = u;
    ++g->dfn_idx;
    for (edge_t* edge = g->node_edges[u]; edge != NULL; edge = edge->next) {
        uint32_t v = edge->sink;
        if (g->dfn[v] == -1) {
            g->par[v] = u;
            dfs_graph(g, v);
        }
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

void lengauer(graph_t* g, graph_t* inv_g) {
    dfs_graph(g, g->entry);
    for (int i = 0; i < g->node_cnt; ++i) {
        g->djs[i] = g->djs_val[i] = g->sdom[i] = i;
    }
    for (int i = g->dfn_idx - 1; i > 0; --i) {
        uint32_t u = g->dfn_node[i];
        for (edge_t* edge = inv_g->node_edges[u]; edge != NULL;
             edge = edge->next) {
            uint32_t v = edge->sink;

            if (g->dfn[v] < g->dfn[u]) {
                if (g->dfn[v] < g->dfn[g->sdom[u]]) {
                    g->sdom[u] = v;
                }

            } else {
                uint32_t djs_v = djs_find(g, v);
                uint32_t sdom = g->sdom[u], sdom_c = g->djs_val[djs_v];
                if (g->dfn[sdom_c] < g->dfn[sdom]) {
                    g->sdom[u] = sdom_c;
                }
            }
        }

        g->djs_val[u] = g->sdom[u];
        g->djs[u] = g->par[u];

        /* printf("sdom %d: %d\n", g->nodes[u].pid, g->nodes[g->sdom[u]].pid); */

        insert_sdom_edge(g, g->sdom[u], u, 0);
        for (edge_t* edge = g->sdom_edges[g->par[u]]; edge != NULL;
             edge = edge->next) {
            uint32_t v = edge->sink, djs_v = djs_find(g, v);
            if (g->dfn[g->sdom[djs_v]] < g->dfn[g->sdom[v]]) {
                g->idom[v] = djs_v;
            } else {
                g->idom[v] = g->par[u];
            }
            --g->sdom_edge_cnt;
        }
        g->sdom_edges[g->par[u]] = NULL;
    }

    for (int i = 1; i < g->dfn_idx; ++i) {
        uint32_t u = g->dfn_node[i];

        if (g->idom[u] != g->sdom[u]) {
            g->idom[u] = g->idom[g->idom[u]];
        }

        /* printf("idom[%d]: %d\n", g->nodes[u].pid, g->nodes[g->idom[u]].pid); */
    }
}

void top_sort_graph_with_OP_distance(graph_t* g) {
    uint32_t queue[MAX_NNODE];
    uint32_t front = 0, back = 0;

    memset(g->OP_dist, 0xff, sizeof(g->OP_dist));
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

#define TIME_WINDOW (10000)
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
        if (diff_set[i])
            printf("%d:%s differ\n", i, opcode_info[i].name);
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
                    compare_paths(g, p1->path, p2->path);
                    printf("\n");
                }
            }
        }
    }
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
    lengauer(&inv_g, &g);
    analyze_branching_subgraph(&g);
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
