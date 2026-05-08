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
    procedure PrintSection(label, G, C, Pi_C, Pi_global)
        ("==SECTION " cat label cat "==");
        PrintIsogenyGraphForSage(G, C, Pi_C);
        printf "global_num_levels=%o\n", #Pi_global;
        printf "global_level_indices=%o\n", GlobalLevelIndices(Pi_C, Pi_global);
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
    G, vert, Pi := ComputeIsogenyGraph(h, D);
    comps_F3 := SortByMinVertex(
        [Component(Random(c)) : c in StronglyConnectedComponents(G)], G);
    for i in [1..#comps_F3] do
        Pi_C := RestrictPartition(G, comps_F3[i], Pi);
        PrintSection("F3_comp_" cat IntegerToString(i), G, comps_F3[i], Pi_C, Pi);
    end for;

    // ---------------------------------------------------------------
    // F9 graph: all components of every size
    // ---------------------------------------------------------------
    h2 := WeilBaseChange(h, 2);
    G2, vert2, Pi2 := ComputeIsogenyGraph(h2, D);
    comps2 := [Component(Random(c)) : c in StronglyConnectedComponents(G2)];

    for sz in [17, 32, 49, 94] do
        group := SortByMinVertex([C : C in comps2 | #Vertices(C) eq sz], G2);
        for i in [1..#group] do
            Pi_C := RestrictPartition(G2, group[i], Pi2);
            label := IntegerToString(sz) cat "_" cat IntegerToString(i);
            PrintSection("F9_" cat label, G2, group[i], Pi_C, Pi2);
        end for;
    end for;
