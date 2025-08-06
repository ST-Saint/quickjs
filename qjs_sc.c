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

typedef struct function_object_t {
    const char* func_name;
    uint8_t* bytecode_buf;
    uint32_t bytecode_len;
} function_object_t;

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
    const char* opstr;
} node_t;

typedef struct edge_t {
    uint32_t src;
    uint32_t sink;
    uint32_t weight;
    struct edge_t* next;
} edge_t;

#define MAX_NNODE (1 << 12)
typedef struct graph_t {
    node_t nodes[MAX_NNODE];
    uint32_t pc_id[MAX_NNODE];
    uint32_t node_cnt;

    edge_t* edges[MAX_NNODE];
    edge_t edge_list[1 << 16];
    uint32_t edge_cnt;

    edge_t* sdom_edges[MAX_NNODE];
    edge_t sdom_edge_list[1 << 16];
    uint32_t sdom_edge_cnt;

    uint32_t dfn[MAX_NNODE];
    uint32_t dfn_idx;
    uint32_t dfn_node[MAX_NNODE];
    uint32_t par[MAX_NNODE];
    uint32_t djs[MAX_NNODE];
    int32_t djs_val[MAX_NNODE];
    uint32_t sdom[MAX_NNODE];
    uint32_t idom[MAX_NNODE];
    uint32_t entry, exit;
} graph_t;

graph_t g, inv_g;

void insert_sdom_edge(graph_t* g,
                      uint32_t src_id,
                      uint32_t sink_id,
                      uint32_t weight) {
    g->sdom_edge_list[g->sdom_edge_cnt] = (edge_t){.src = src_id,
                                              .sink = sink_id,
                                              .weight = weight,
                                              .next = g->sdom_edges[src_id]};
    g->sdom_edges[src_id] = &g->sdom_edge_list[g->sdom_edge_cnt++];
}

void insert_edge(graph_t* g,
                 uint32_t src_id,
                 uint32_t sink_id,
                 uint32_t weight) {
    g->edge_list[g->edge_cnt] = (edge_t){.src = src_id,
                                         .sink = sink_id,
                                         .weight = weight,
                                         .next = g->edges[src_id]};
    g->edges[src_id] = &g->edge_list[g->edge_cnt++];
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
    inv_g->node_cnt = g->node_cnt;
    inv_g->entry = g->exit;
    inv_g->exit = g->entry;
    for (int i = 0; i < g->edge_cnt; ++i) {
        edge_t* edge = &g->edge_list[i];
        insert_edge(inv_g, edge->sink, edge->src, edge->weight);
    }
}

void parse_bytecodes(function_object_t* func_obj, uint32_t* exec_time) {
    uint8_t* base = func_obj->bytecode_buf;
    uint8_t *pc = func_obj->bytecode_buf, *next_pc;
    uint32_t inst_cnt = 0;
    int8_t jump_offset;
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
        node->opstr = opcode_info[*pc].name;

        switch (*pc) {
            case OP_if_false:
            case OP_if_true:
            case OP_goto:
            case OP_goto16:
                printf("WARN: not implemented");
                assert(0);
                break;
            case OP_goto8:
                jump_offset = *(pc + 1);
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
            case OP_if_true8:
            case OP_if_false8:
                jump_offset = *(pc + 1);
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
    for (edge_t* edge = g->edges[u]; edge != NULL; edge = edge->next) {
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
        for (edge_t* edge = inv_g->edges[u]; edge != NULL; edge = edge->next) {
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
        for (edge_t* edge = g->sdom_edges[g->par[u]]; edge != NULL; edge = edge->next) {
            uint32_t v =edge->sink, djs_v=djs_find(g, v);
            if( g->dfn[g->sdom[djs_v]] < g->dfn[g->sdom[v]]){
                g->idom[v] = djs_v;
            }else{
                g->idom[v]=g->par[u];
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

        printf("idom %d: %d\n", g->nodes[u].pid, g->nodes[g->idom[u]].pid);
    }
}

void sc_analyze(const char* func_name, const char* profile_file) {
    function_object_t* func_obj = load_func_bytecode(func_name);
    uint32_t* exec_time = NULL;
    if (profile_file) {
        exec_time = load_exec_time(func_obj, profile_file);
    } else {
        exec_time = malloc(sizeof(uint32_t) * func_obj->bytecode_len);
        memset(exec_time, 0, sizeof(uint32_t) * func_obj->bytecode_len);
    }
    parse_bytecodes(func_obj, exec_time);
    lengauer(&inv_g, &g);
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
