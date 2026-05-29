/*
    Generate PrintIsogenyGraphForSage data for all paper figures.
    Output is split into sections by ==SECTION <name>== markers so that
    a post-processing script can split them into separate data files.

    Each section contains:
        edges=[...]
        Pi=[...]
        global_num_levels=N          (total cells in the global Pi for this graph)
        global_level_indices=[i,...] (0-indexed position of each Pi cell in the global Pi)

    The global_* lines allow the plotting script to use consistent colors across
    separate plots of different components of the same graph.

    Usage:
        magma -b magma_gen_all_plots.m > all_plots_raw.txt
        python3 magma_split_sections.py all_plots_raw.txt plot_data/
        bash gen_v4_plots.sh
*/
    AttachSpec("spec");
    _<x> := PolynomialRing(Integers());

    h := x^8 + 2*x^7 - x^6 - 5*x^5 - 8*x^4 - 15*x^3 - 9*x^2 + 54*x + 81;
    D := 2;

    // For each cell in Pi0, find its 0-indexed position in Pi_global.
    function GlobalLevelIndices(Pi0, Pi_global)
        result := [];
        for cell in Pi0 do
            v := cell[1];
            gl := [i - 1 : i in [1..#Pi_global] | v in Pi_global[i]][1];
            Append(~result, gl);
        end for;
        return result;
    end function;

    // Print one section: label, graph data, and global color info.
    //   global_num_levels        = #Pi_global, controls color spread
    //   global_level_indices     = position of each Pi_C cell in Pi_global, controls per-vertex color
    //   global_max_local_levels  = max #Pi_C across siblings, controls canvas extent
    procedure PrintSection(label, G, C, Pi_C, Pi_global, max_local_levels)
        ("==SECTION " cat label cat "==");
        PrintIsogenyGraphForSage(G, C, Pi_C);
        printf "global_num_levels=%o\n", #Pi_global;
        printf "global_level_indices=%o\n", GlobalLevelIndices(Pi_C, Pi_global);
        printf "global_max_local_levels=%o\n", max_local_levels;
    end procedure;

    // Sort components by minimum vertex index for a stable ordering.
    function SortByMinVertex(comps, G)
        V := Vertices(G);
        return Sort(comps,
            func<a, b | Min([Index(V, v) : v in Vertices(a)])
                      - Min([Index(V, v) : v in Vertices(b)])>);
    end function;

    // ---------------------------------------------------------------
    // F3 graph: all SCCs, one section per component
    // ---------------------------------------------------------------
    G, _, _, Pi := ComputeIsogenyGraph(h, D);
    comps_F3 := SortByMinVertex(
        [Component(Random(c)) : c in StronglyConnectedComponents(G)], G);
    Pi_C_F3 := [RestrictPartition(G, C, Pi) : C in comps_F3];
    max_local_F3 := Max([#p : p in Pi_C_F3]);
    for i in [1..#comps_F3] do
        PrintSection("F3_comp_" cat IntegerToString(i),
                     G, comps_F3[i], Pi_C_F3[i], Pi, max_local_F3);
    end for;

    // ---------------------------------------------------------------
    // F9 graph: all components of every size
    // ---------------------------------------------------------------
    h2 := WeilBaseChange(h, 2);
    G2, _, _, Pi2 := ComputeIsogenyGraph(h2, D);
    comps2 := [Component(Random(c)) : c in StronglyConnectedComponents(G2)];
    // Cache the restricted partition once per component (used for both the
    // canvas-extent maximum below and the per-section output).
    Pi_C_F9 := [RestrictPartition(G2, C, Pi2) : C in comps2];
    max_local_F9 := Max([#p : p in Pi_C_F9]);

    // Compute the distinct component sizes dynamically rather than hardcoding.
    V2 := Vertices(G2);
    sizes := Sort(SetToSequence({#Vertices(C) : C in comps2}));
    for sz in sizes do
        // Indices of the components of this size, sorted by min vertex index
        // for a stable ordering (matching SortByMinVertex on the components).
        idxs := Sort([i : i in [1..#comps2] | #Vertices(comps2[i]) eq sz],
            func<a, b | Min([Index(V2, v) : v in Vertices(comps2[a])])
                      - Min([Index(V2, v) : v in Vertices(comps2[b])])>);
        for i in [1..#idxs] do
            ci := idxs[i];
            label := IntegerToString(sz) cat "_" cat IntegerToString(i);
            PrintSection("F9_" cat label, G2, comps2[ci], Pi_C_F9[ci], Pi2, max_local_F9);
        end for;
    end for;
