"""
plot_isogeny_graph.sage — Automatic isogeny graph layout and export.

Usage:
    sage plot_isogeny_graph.sage <data_file> <output_file> [r0]

Arguments:
    data_file    Text file containing the output of PrintIsogenyGraphForSage (Magma).
                 Must contain two lines of the form:
                     edges=[ [a,b], [c,d], ... ]
                     Pi=[ [v1,v2,...], [w1,...], ... ]
    output_file  Output path; extension determines format (.png, .pdf, .svg).
    r0           Optional ring spacing in data units (default: 1.5).

Pipeline:
    1. In Magma, run PrintIsogenyGraphForSage and redirect output to a file:
           magma -b my_script.m > edges.txt
    2. Run this script:
           sage plot_isogeny_graph.sage edges.txt my_graph.pdf

Layout algorithm (concentric rings + DFS minor cluster ordering):
    - Pi is sorted ascending by cell size; level 0 (smallest cell) sits at center.
    - Within each level, vertices are grouped into minor clusters: connected
      components of the subgraph induced by all vertices up to that level,
      further split so that any two vertices in a cluster have undirected
      distance <= 2.
    - A minor cluster tree is built, and a lex_DFS traversal determines the
      angular ordering of clusters around each ring.
    - Vertices are placed at radius level * r0, uniformly spaced by DFS order.
"""

import sys
from math import pi, cos, sin, sqrt, atan2


# ---------------------------------------------------------------------------
# Input parsing
# ---------------------------------------------------------------------------

def parse_input(filename):
    """Parse output of PrintIsogenyGraphForSage into (edges, Pi)."""
    with open(filename) as f:
        content = f.read()
    start = content.find('edges=[')
    if start == -1:
        raise ValueError("Could not find 'edges=[' in %s" % filename)
    snippet = content[start:]
    namespace = {}
    exec(compile(snippet, filename, 'exec'), namespace)
    return namespace['edges'], namespace['Pi']


# ---------------------------------------------------------------------------
# Coloring: orange (level 0, center) to yellow (outermost)
# ---------------------------------------------------------------------------

def make_color_rgb(level_index, num_levels):
    t = level_index / max(num_levels - 1, 1)
    g = int(t * 255)
    return (1.0, g / 255.0, 0.0)


# ---------------------------------------------------------------------------
# Layout algorithm
# ---------------------------------------------------------------------------

def kill_repeats(lst):
    seen = []
    for x in lst:
        if x not in seen:
            seen.append(x)
    return seen


def compute_layout(G_sage, Pi_sorted, r0=1.5):
    n_levels = len(Pi_sorted)

    vertex_level = {}
    for l, cell in enumerate(Pi_sorted):
        for v in cell:
            vertex_level[v] = l

    # Gfil[k] = undirected subgraph of Pi[k+1 .. n-1] (the OUTER rings above level k).
    # Matching the original notebook: Gfil is built from Pi reversed then re-reversed so that
    # Gfil[i-1] = subgraph of Pi[i .. n-1], used for minor-cluster construction at level i.
    Gfil = {}
    for k in range(n_levels):
        verts = [v for l in range(k + 1, n_levels) for v in Pi_sorted[l]]
        Gfil[k] = G_sage.subgraph(verts).to_undirected()

    minor_cluster_dict = {0: [list(Pi_sorted[0])]}
    for i in range(1, n_levels):
        # Gun = outer subgraph Pi[i .. n-1]; Pi[i] vertices are all present in Gun.
        Gun = Gfil[i - 1]
        remaining = list(Pi_sorted[i])
        minor_cluster_dict[i] = []
        while remaining:
            x = remaining[0]
            comp = set(Gun.connected_component_containing_vertex(x))
            part_in_comp = [y for y in remaining if y in comp]
            cluster = [y for y in part_in_comp if Gun.distance(x, y) <= 2]
            if not cluster:
                cluster = [x]
            minor_cluster_dict[i].append(cluster)
            cluster_set = set(cluster)
            remaining = [v for v in remaining if v not in cluster_set]

    minor_clusters = []
    for i in range(n_levels):
        minor_clusters.extend(minor_cluster_dict[i])

    def get_minor_cluster(v):
        l = vertex_level[v]
        for mc in minor_cluster_dict[l]:
            if v in mc:
                return mc
        raise ValueError("Vertex %s not found in minor clusters" % v)

    mc_index = {id(mc): i for i, mc in enumerate(minor_clusters)}

    mc_edge_set = set()
    for i in range(n_levels - 1):
        for mc in minor_cluster_dict[i]:
            reachable_mcs = []
            for v in mc:
                for w in G_sage.neighbors_out(v):
                    if vertex_level.get(w) == i + 1:
                        reachable_mcs.append(get_minor_cluster(w))
            for mc_next in kill_repeats(reachable_mcs):
                src = mc_index[id(mc)]
                dst = mc_index[id(mc_next)]
                if src != dst:
                    mc_edge_set.add((src, dst))

    mc_edges = list(mc_edge_set)
    if mc_edges:
        mc_graph = Graph(mc_edges)
    else:
        mc_graph = Graph(len(minor_clusters))

    root_mc = minor_cluster_dict[0][0]
    i0 = mc_index[id(root_mc)]
    dfs = mc_graph.lex_DFS(initial_vertex=i0) if minor_clusters else [i0]
    dfs_rank = {v: k for k, v in enumerate(dfs)}

    def sort_key(v):
        mc = get_minor_cluster(v)
        return dfs_rank.get(mc_index[id(mc)], 0)

    angle_dict = {}
    for cell in Pi_sorted:
        N = len(cell)
        step = 2 * pi / N if N > 0 else 0
        for k, v in enumerate(sorted(cell, key=sort_key)):
            angle_dict[v] = k * step

    pos = {}
    for v in G_sage.vertices():
        l = vertex_level[v]
        r = l * r0
        N = len(Pi_sorted[l])
        offset = pi / N if N > 0 else 0
        alpha = angle_dict.get(v, 0)
        pos[v] = (float(r * cos(alpha + offset)),
                  float(r * sin(alpha + offset)))

    return pos, vertex_level


# ---------------------------------------------------------------------------
# Matplotlib rendering
# ---------------------------------------------------------------------------

def draw_graph(G_sage, pos, vertex_level, Pi_sorted, output_file, r0=1.5,
               vertex_radius=0.12, figsize=12):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    from matplotlib.patches import FancyArrowPatch
    import matplotlib.patheffects as pe
    import numpy as np

    n_levels = len(Pi_sorted)

    fig, ax = plt.subplots(figsize=(figsize, figsize))
    ax.set_aspect('equal')
    ax.axis('off')

    # --- concentric guide circles (dashed gray) ---
    for l in range(1, n_levels):
        r = l * r0
        circle = plt.Circle((0, 0), r, color='#cccccc', fill=False,
                             linestyle='--', linewidth=0.8, zorder=0)
        ax.add_patch(circle)

    # --- detect bidirectional pairs for arc routing ---
    edge_list = [(u, v) for u, v, _ in G_sage.edges()]
    edge_set = set(edge_list)
    # count multiplicity
    from collections import Counter
    edge_count = Counter(edge_list)

    def _angle(p1, p2):
        return atan2(p2[1] - p1[1], p2[0] - p1[0])

    drawn_pairs = set()

    for (u, v), cnt in edge_count.items():
        x1, y1 = pos[u]
        x2, y2 = pos[v]
        bidir = (v, u) in edge_set
        pair_key = (min(u, v), max(u, v))

        # Perpendicular offset for bidirectional edges
        dx = x2 - x1
        dy = y2 - y1
        dist = sqrt(dx*dx + dy*dy) or 1.0
        nx = -dy / dist
        ny = dx / dist

        if bidir:
            offset_scale = vertex_radius * 0.7
            # forward arc (u->v)
            ox1 = x1 + nx * offset_scale
            oy1 = y1 + ny * offset_scale
            ox2 = x2 + nx * offset_scale
            oy2 = y2 + ny * offset_scale
        else:
            ox1, oy1 = x1, y1
            ox2, oy2 = x2, y2

        # Shorten arrow to not overlap vertex circles
        sdx = ox2 - ox1
        sdy = oy2 - oy1
        slen = sqrt(sdx*sdx + sdy*sdy) or 1.0
        shrink = vertex_radius + 0.02
        ax1 = ox1 + sdx / slen * shrink
        ay1 = oy1 + sdy / slen * shrink
        ax2 = ox2 - sdx / slen * shrink
        ay2 = oy2 - sdy / slen * shrink

        arrow = FancyArrowPatch(
            (ax1, ay1), (ax2, ay2),
            arrowstyle='-|>',
            mutation_scale=10,
            color='black',
            linewidth=0.8,
            zorder=1,
        )
        ax.add_patch(arrow)

    # --- vertices ---
    for l, cell in enumerate(Pi_sorted):
        color = make_color_rgb(l, n_levels)
        for v in cell:
            x, y = pos[v]
            circle = plt.Circle((x, y), vertex_radius, color=color,
                                 ec='black', linewidth=0.8, zorder=2)
            ax.add_patch(circle)

    # --- axis limits with padding ---
    all_x = [p[0] for p in pos.values()]
    all_y = [p[1] for p in pos.values()]
    pad = r0 * 0.4
    ax.set_xlim(min(all_x) - pad, max(all_x) + pad)
    ax.set_ylim(min(all_y) - pad, max(all_y) + pad)

    import os
    os.makedirs(os.path.dirname(os.path.abspath(output_file)), exist_ok=True)
    fig.savefig(output_file, bbox_inches='tight', dpi=200)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)

    data_file   = sys.argv[1]
    output_file = sys.argv[2]
    r0          = float(sys.argv[3]) if len(sys.argv) >= 4 else 1.5

    edges, Pi = parse_input(data_file)
    Pi_sorted = sorted(Pi, key=len)
    G_sage = DiGraph(edges, multiedges=True)

    print("Vertices: %d   Edges: %d   Levels: %d" % (
        G_sage.num_verts(), G_sage.num_edges(), len(Pi_sorted)))

    pos, vertex_level = compute_layout(G_sage, Pi_sorted, r0=r0)

    draw_graph(G_sage, pos, vertex_level, Pi_sorted, output_file, r0=r0)
    print("Saved: %s" % output_file)


main()
