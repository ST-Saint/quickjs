import json
import networkx as nx
import matplotlib.pyplot as plt
import argparse

# --- Load the JSON ---
def load_cfg(cfgfile):
    with open(cfgfile) as f:
        cfg_data = json.load(f)
    return cfg_data


# --- Build the graph ---
def build_cfg(nodes, edges):
    G = nx.DiGraph()
    G.add_nodes_from(nodes)
    G.add_edges_from(edges)

    return G


# --- Draw the CFG ---
def draw_cfg(G):
    plt.figure(figsize=(6, 4))
    pos = nx.spring_layout(G)  # or nx.planar_layout, nx.shell_layout, etc.
    nx.draw(G, pos, with_labels=True, node_size=1500, node_color="lightblue", arrows=True)
    nx.draw_networkx_edge_labels(G, pos, edge_labels={(u, v): f"{u}->{v}" for u, v in edges})
    plt.title("Control Flow Graph")
    #plt.show()


def dfs_paths(graph, start, goal, path=None):
    if path is None:
        path = [start]
    if start == goal:
        return [path]
    paths = []
    for nxt in graph.successors(start):
        if nxt not in path:  # avoid cycles
            paths.extend(dfs_paths(graph, nxt, goal, path + [nxt]))
    return paths


# --- Find all control flow paths ---
def list_cf_paths(G):
    # an entry: no incoming edges and
    # exit: no outgoing edges
    entries = [n for n in G.nodes if G.in_degree(n) == 0]
    exits = [n for n in G.nodes if G.out_degree(n) == 0]

    all_paths = []
    for entry in entries:
        for exit_node in exits:
            all_paths.extend(dfs_paths(G, entry, exit_node))

    return all_paths


def print_cf_paths(all_paths, nodes):
    print("All control flow paths:")
    #for p in all_paths:
    #    print(" -> ".join(p))

    pathcnt = 0
    for path in all_paths:
        cnt = 0
        pathstr = f"[PATH {pathcnt}] => "
        for p in path:
            label = nodes[int(p)]["label"]
            if (cnt == 0):
                pathstr += f"{label}"
            else:
                pathstr += f" -> {label}"
            cnt += 1
        print(pathstr)
        pathcnt += 1


def parse_arguments():
    parser = argparse.ArgumentParser(description="Generate instruction cf paths")
    parser.add_argument("-c", "--cfgfile", default=".bytecode/<fname>.json",
        help="Control flow graph file in json format")
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_arguments()
    cfgfile = args.cfgfile

    cfg_data = load_cfg(cfgfile)

    nodes = cfg_data["nodes"]
    edges = [(e["source"], e["target"]) for e in cfg_data["links"]]
    node_ids = [ n["id"] for n in nodes ]

    G = build_cfg(node_ids, edges)

    draw_cfg(G)

    all_paths = list_cf_paths(G)

    print_cf_paths(all_paths, nodes)
