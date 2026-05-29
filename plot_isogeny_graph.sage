"""
plot_isogeny_graph.sage — Automatic isogeny graph layout and export.

Usage:
    sage plot_isogeny_graph.sage <data_file> <output_file> [r0] [target_scale]

Arguments:
    data_file    Text file containing the output of PrintIsogenyGraphForSage (Magma).
                 Must contain two lines of the form:
                     edges=[ [a,b], [c,d], ... ]
                     Pi=[ [v1,v2,...], [w1,...], ... ]
    output_file  Output path; extension determines format (.png, .pdf, .svg).
    r0           Optional ring spacing in data units (default: 1.5).
    target_scale Optional. The intended \\includegraphics scale=... in paper.tex
                 (e.g. 0.1, 0.23, 0.33). When provided, vertex circles and arrow
                 dimensions are enlarged by 1/target_scale so that the printed
                 result has constant absolute size across figures with different
                 LaTeX scales.

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
    - A minor cluster graph is built, and an iterative DFS over the minor
      cluster graph (which may be disconnected for components above the crater)
      determines the angular ordering of clusters around each ring.
    - Vertices are placed at radius level * r0, uniformly spaced by DFS order.
"""

import sys
from math import pi, cos, sin, sqrt, atan2


# ---------------------------------------------------------------------------
# Input parsing
# ---------------------------------------------------------------------------

def parse_input(filename):
    """Parse output of PrintIsogenyGraphForSage.

    Returns (edges, Pi, global_num_levels, global_level_indices, global_max_local_levels).
    Trailing fields are None if absent (older format without cross-component
    color/scale consistency).
    """
    with open(filename) as f:
        content = f.read()
    start = content.find('edges=[')
    if start == -1:
        raise ValueError("Could not find 'edges=[' in %s" % filename)
    snippet = content[start:]
    namespace = {}
    exec(compile(snippet, filename, 'exec'), namespace)
    return (namespace['edges'],
            namespace['Pi'],
            namespace.get('global_num_levels', None),
            namespace.get('global_level_indices', None),
            namespace.get('global_max_local_levels', None))


# ---------------------------------------------------------------------------
# Coloring: orange (level 0, center) to yellow (outermost)
# ---------------------------------------------------------------------------

def make_color_rgb(global_level_index, global_num_levels):
    """Map a global level index to an RGB color (orange=innermost, yellow=outermost).

    Using global_level_index / global_num_levels ensures that the same order type
    gets the same color across separate plots of different components of the same graph.

    The divisor is global_num_levels (not global_num_levels - 1) to match the
    historical figure convention: the outermost ring lands at ~75% yellow rather
    than pure yellow.
    """
    t = global_level_index / max(global_num_levels, 1)
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
        mc_graph = Graph()
    # Ensure every minor cluster index is a vertex (isolated clusters must still rank)
    mc_graph.add_vertices(list(range(len(minor_clusters))))

    root_mc = minor_cluster_dict[0][0]
    i0 = mc_index[id(root_mc)]

    # Standard iterative DFS that visits all children of a node before
    # backtracking — this keeps sibling clusters adjacent in the ordering.
    # lex_DFS is NOT used because it can interleave children from different
    # parents, splitting clusters that should be angularly adjacent.
    def _dfs(start, visited):
        result = []
        stack = [start]
        while stack:
            v = stack.pop()
            if v not in visited:
                visited.add(v)
                result.append(v)
                for w in sorted(mc_graph.neighbors(v), reverse=True):
                    if w not in visited:
                        stack.append(w)
        return result

    dfs = []
    visited = set()
    seeds = [i0] + [j for j in range(len(minor_clusters)) if j != i0]
    for seed in seeds:
        if seed not in visited:
            dfs.extend(_dfs(seed, visited))

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
               figsize=12, target_scale=None,
               global_num_levels=None, global_level_indices=None,
               global_max_local_levels=None):
    """Render the graph to PNG.

    target_scale: the eventual \\includegraphics scale=... in paper.tex.
    When provided, vertex circles, arrow line widths, and arrowhead sizes are
    enlarged by 1/target_scale so the printed result has constant absolute size
    regardless of how each figure is scaled in the LaTeX layout.
    """
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyArrowPatch

    # Determine canvas data extent before computing scaled dimensions.
    pad = r0 * 0.4
    if global_max_local_levels is not None:
        extent = (global_max_local_levels - 1) * r0 + pad
    else:
        all_x = [p[0] for p in pos.values()]
        all_y = [p[1] for p in pos.values()]
        extent = max(max(all_x), max(all_y), -min(all_x), -min(all_y)) + pad
    data_extent_total = 2.0 * extent
    figsize_pt = figsize * 72.0  # figure size in points

    # Compute rendering dimensions. When target_scale is set, every quantity
    # below is sized so that (PNG size) * target_scale = a fixed printed size,
    # uniform across figures with different intended LaTeX scales.
    if target_scale is not None and float(target_scale) > 0:
        s = float(target_scale)
        TARGET_VERTEX_RADIUS_PT = 3.0
        TARGET_LINEWIDTH_PT     = 0.8
        TARGET_RING_LW_PT       = 0.15
        # vertex_radius_data = (target_pt_natural) * (data_per_pt)
        #                    = (TARGET_RADIUS_PT / s) * (data_extent_total / figsize_pt)
        vertex_radius  = TARGET_VERTEX_RADIUS_PT * data_extent_total / (figsize_pt * s)
        linewidth      = TARGET_LINEWIDTH_PT / s
        mutation_scale = linewidth * 5.6   # arrowhead size proportional to lw (matches old 28/5 ratio)
        ring_lw        = TARGET_RING_LW_PT / s
    else:
        vertex_radius  = 0.28
        linewidth      = 5.0
        mutation_scale = 28.0
        ring_lw        = 0.8

    n_levels = len(Pi_sorted)

    fig, ax = plt.subplots(figsize=(figsize, figsize))
    ax.set_aspect('equal')
    ax.axis('off')

    # --- concentric guide circles (dashed gray) ---
    # Draw rings up to the deepest component in the parent graph so every
    # component renders to the same canvas size.
    ring_levels = global_max_local_levels if global_max_local_levels is not None else n_levels
    for l in range(1, ring_levels):
        r = l * r0
        circle = plt.Circle((0, 0), r, color='#cccccc', fill=False,
                             linestyle='--', linewidth=ring_lw, zorder=0)
        ax.add_patch(circle)

    # --- detect bidirectional pairs ---
    edge_list = [(u, v) for u, v, _ in G_sage.edges()]
    edge_set = set(edge_list)
    from collections import Counter
    edge_count = Counter(edge_list)

    # Each distinct (u, v) is drawn at most once. Parallel directed edges of the
    # same orientation (multiplicity > 1) collapse into a single arrow; warn once
    # so a multigraph with parallel edges is not silently misrepresented.
    if any(cnt > 1 for cnt in edge_count.values()):
        sys.stderr.write(
            "WARNING: parallel directed edges detected (multiplicity > 1); "
            "they are rendered as a single arrow.\n")

    drawn_pairs = set()

    for (u, v) in edge_count:
        bidir = (v, u) in edge_set
        pair_key = (min(u, v), max(u, v))
        if bidir and pair_key in drawn_pairs:
            continue
        drawn_pairs.add(pair_key)

        x1, y1 = pos[u]
        x2, y2 = pos[v]

        # Shorten arrow to not overlap vertex circles
        sdx = x2 - x1
        sdy = y2 - y1
        slen = sqrt(sdx*sdx + sdy*sdy) or 1.0
        shrink = vertex_radius + 0.02
        ax1 = x1 + sdx / slen * shrink
        ay1 = y1 + sdy / slen * shrink
        ax2 = x2 - sdx / slen * shrink
        ay2 = y2 - sdy / slen * shrink

        arrow = FancyArrowPatch(
            (ax1, ay1), (ax2, ay2),
            arrowstyle='<|-|>' if bidir else '-|>',
            mutation_scale=mutation_scale,
            color='black',
            linewidth=linewidth,
            zorder=1,
        )
        ax.add_patch(arrow)

    # --- vertices ---
    # Use global level indices when available so the same endo ring gets the
    # same color across separate plots of different components.
    g_n = global_num_levels if global_num_levels is not None else n_levels
    g_idx = global_level_indices if global_level_indices is not None else list(range(n_levels))
    for l, cell in enumerate(Pi_sorted):
        color = make_color_rgb(g_idx[l], g_n)
        for v in cell:
            x, y = pos[v]
            circle = plt.Circle((x, y), vertex_radius, color=color,
                                 ec='black', linewidth=linewidth, zorder=2)
            ax.add_patch(circle)

    # --- axis limits ---
    ax.set_xlim(-extent, extent)
    ax.set_ylim(-extent, extent)

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

    data_file    = sys.argv[1]
    output_file  = sys.argv[2]
    r0           = float(sys.argv[3]) if len(sys.argv) >= 4 else 1.5
    target_scale = float(sys.argv[4]) if len(sys.argv) >= 5 else None

    edges, Pi, global_num_levels, global_level_indices, global_max_local_levels = parse_input(data_file)
    Pi_sorted = sorted(Pi, key=len)
    G_sage = DiGraph(edges, multiedges=True)

    print("Vertices: %d   Edges: %d   Levels: %d   target_scale=%s" % (
        G_sage.num_verts(), G_sage.num_edges(), len(Pi_sorted), target_scale))

    pos, vertex_level = compute_layout(G_sage, Pi_sorted, r0=r0)

    draw_graph(G_sage, pos, vertex_level, Pi_sorted, output_file, r0=r0,
               target_scale=target_scale,
               global_num_levels=global_num_levels,
               global_level_indices=global_level_indices,
               global_max_local_levels=global_max_local_levels)
    print("Saved: %s" % output_file)


if __name__ == '__main__':
    main()
