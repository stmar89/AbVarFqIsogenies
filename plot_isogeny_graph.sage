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
    r0           Optional ring spacing in pixels (default: 300).

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
from math import pi, cos, sin


# ---------------------------------------------------------------------------
# Input parsing
# ---------------------------------------------------------------------------

def parse_input(filename):
    """Parse output of PrintIsogenyGraphForSage into (edges, Pi).

    Extracts the edges=[...] and Pi=[...] blocks from the file, ignoring
    any other output (e.g. vertex/edge counts printed by the Magma script).
    """
    with open(filename) as f:
        content = f.read()
    # Find the edges block: from 'edges=[' to the closing ']]'
    start = content.find('edges=[')
    if start == -1:
        raise ValueError("Could not find 'edges=[' in %s" % filename)
    snippet = content[start:]
    namespace = {}
    exec(compile(snippet, filename, 'exec'), namespace)
    return namespace['edges'], namespace['Pi']


# ---------------------------------------------------------------------------
# Coloring
# ---------------------------------------------------------------------------

def make_color(level_index, num_levels):
    """Orange-to-yellow gradient: level 0 (highest ring) is darkest orange."""
    rgbv = int(level_index * 255 / num_levels)
    return '#%02x%02x%02x' % (255, rgbv, 0)


# ---------------------------------------------------------------------------
# Layout algorithm
# ---------------------------------------------------------------------------

def kill_repeats(lst):
    seen = []
    for x in lst:
        if x not in seen:
            seen.append(x)
    return seen


def compute_layout(G_sage, Pi_sorted, r0=300):
    """
    Return a position dict {vertex: (x, y)} using concentric rings with
    angular order determined by a lex_DFS traversal of the minor cluster tree.

    Parameters
    ----------
    G_sage     : SageMath DiGraph (multiedges allowed)
    Pi_sorted  : list of lists, partition of vertex indices sorted ascending
                 by cell size (level 0 = center = smallest cell)
    r0         : ring spacing in pixels
    """
    n_levels = len(Pi_sorted)

    # Map each vertex to its level index
    vertex_level = {}
    for l, cell in enumerate(Pi_sorted):
        for v in cell:
            vertex_level[v] = l

    # ------------------------------------------------------------------
    # Build undirected filtered subgraphs.
    # Gfil[k] = undirected subgraph induced by vertices at levels 0..k+1.
    # Used for minor cluster construction at level k+1.
    # ------------------------------------------------------------------
    Gfil = {}
    for k in range(n_levels - 1):
        verts = [v for l in range(k + 2) for v in Pi_sorted[l]]
        Gfil[k] = G_sage.subgraph(verts).to_undirected()

    # ------------------------------------------------------------------
    # Minor clusters.
    # Level 0: one cluster containing all level-0 vertices.
    # Level i > 0: split Pi[i] by (a) connected component in Gfil[i-1]
    #              and (b) undirected distance <= 2 within that component.
    # ------------------------------------------------------------------
    minor_cluster_dict = {0: [list(Pi_sorted[0])]}

    for i in range(1, n_levels):
        Gun = Gfil[i - 1]
        remaining = list(Pi_sorted[i])
        minor_cluster_dict[i] = []

        while remaining:
            x = remaining[0]
            if Gun.has_vertex(x):
                comp = set(Gun.connected_component_containing_vertex(x))
                part_in_comp = [y for y in remaining if y in comp]
                cluster = [y for y in part_in_comp
                           if Gun.distance(x, y) <= 2]
            else:
                cluster = [x]
            minor_cluster_dict[i].append(cluster)
            cluster_set = set(cluster)
            remaining = [v for v in remaining if v not in cluster_set]

    # Flattened list of all minor clusters (order matters for DFS indexing)
    minor_clusters = []
    for i in range(n_levels):
        minor_clusters.extend(minor_cluster_dict[i])

    # ------------------------------------------------------------------
    # Lookup helpers
    # ------------------------------------------------------------------
    def get_minor_cluster(v):
        l = vertex_level[v]
        for mc in minor_cluster_dict[l]:
            if v in mc:
                return mc
        raise ValueError("Vertex %s not found in minor clusters" % v)

    def get_minor_clusters_for(major_cluster):
        return kill_repeats([get_minor_cluster(v) for v in major_cluster])

    # ------------------------------------------------------------------
    # Minor cluster tree edges.
    # Edge from mc_A (level l) to mc_B (level l+1) if any vertex of mc_A
    # has an outgoing edge (in the directed isogeny graph) to any vertex
    # whose minor cluster is mc_B.
    # ------------------------------------------------------------------
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

    # Build undirected graph on minor clusters for lex_DFS
    if mc_edges:
        mc_graph = Graph(mc_edges)
    else:
        mc_graph = Graph(len(minor_clusters))

    # ------------------------------------------------------------------
    # lex_DFS from the root (level-0 minor cluster)
    # ------------------------------------------------------------------
    root_mc = minor_cluster_dict[0][0]
    i0 = mc_index[id(root_mc)]

    if minor_clusters:
        dfs = mc_graph.lex_DFS(initial_vertex=i0)
    else:
        dfs = [i0]

    dfs_rank = {v: k for k, v in enumerate(dfs)}

    def sort_key(v):
        mc = get_minor_cluster(v)
        return dfs_rank.get(mc_index[id(mc)], 0)

    # ------------------------------------------------------------------
    # Assign angles within each ring by DFS order
    # ------------------------------------------------------------------
    angle_dict = {}
    for cell in Pi_sorted:
        N = len(cell)
        step = 2 * pi / N if N > 0 else 0
        for k, v in enumerate(sorted(cell, key=sort_key)):
            angle_dict[v] = k * step

    # ------------------------------------------------------------------
    # Convert polar -> Cartesian
    # ------------------------------------------------------------------
    pos = {}
    for v in G_sage.vertices():
        l = vertex_level[v]
        r = l * r0
        N = len(Pi_sorted[l])
        offset = pi / N if N > 0 else 0
        alpha = angle_dict.get(v, 0)
        pos[v] = (float(r * cos(alpha + offset)),
                  float(r * sin(alpha + offset)))

    return pos


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

    # Sort Pi ascending by cell size (level 0 = center = fewest vertices)
    Pi_sorted = sorted(Pi, key=len)

    # Build SageMath DiGraph
    G_sage = DiGraph(edges, multiedges=True)

    print("Vertices: %d   Edges: %d   Levels: %d" % (
        G_sage.num_verts(), G_sage.num_edges(), len(Pi_sorted)))

    # Compute layout
    pos = compute_layout(G_sage, Pi_sorted, r0=r0)

    # Build vertex color dict {color: [vertices]}
    vertex_colors = {}
    n = len(Pi_sorted)
    for l, cell in enumerate(Pi_sorted):
        c = make_color(l, n)
        vertex_colors[c] = list(cell)

    # Plot
    fig = G_sage.plot(
        pos=pos,
        vertex_colors=vertex_colors,
        vertex_size=800,
        color_by_label=False,
        vertex_labels=False,
        figsize=[12, 12],
    )
    fig.save(output_file)
    print("Saved: %s" % output_file)


main()
