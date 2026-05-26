/*
    Example 1.1

    This example is about the 2-isogenies in the isogeny class 4.3.c_ab_af_ai of abelian varieties over F3,
    and of its extension to F9.

    To adapt this example to a different isogeny class, replace h with your Weil polynomial and
    adjust D to the desired isogeny degree.

    Run from the AbVarFqIsogenies/ directory.
    This code is paired with isogeny-graphs.ipynb for the graphical outputs.
*/

    AttachSpec("spec");
    _<x> := PolynomialRing(Integers());

    // ---------------------------------------------------------------
    // 2-isogeny graph over F3
    // ---------------------------------------------------------------

    h := x^8 + 2*x^7 - x^6 - 5*x^5 - 8*x^4 - 15*x^3 - 9*x^2 + 54*x + 81;
    D := 2;
    G, vert, Pi := ComputeIsogenyGraph(h, D);
    "Number of vertices:", #vert;
    "Number of edges:", #Edges(G);

    // ---------------------------------------------------------------
    // 2-isogeny graph of the base change to F9
    // ---------------------------------------------------------------

    h2 := WeilBaseChange(h, 2);
    G2, vert2, Pi2 := ComputeIsogenyGraph(h2, D);
    "Number of vertices (F9):", #vert2;

    // Find isomorphism classes of strongly connected components
    comps := [Component(Random(c)) : c in StronglyConnectedComponents(G2)];
    classes := [];
    for Gc in comps do
        if not exists{Gd : Gd in classes | IsIsomorphic(UnderlyingDigraph(Gc), UnderlyingDigraph(Gd))} then
            Append(~classes, Gc);
        end if;
    end for;
    "Number of isomorphism classes of components:", #classes;
    "Component sizes (vertices, count):";
    comp_sizes := AssociativeArray();
    for C in comps do
        s := #Vertices(C);
        if IsDefined(comp_sizes, s) then
            comp_sizes[s] +:= 1;
        else
            comp_sizes[s] := 1;
        end if;
    end for;
    [<s, comp_sizes[s]> : s in Sort([k : k in Keys(comp_sizes)])];

    // ---------------------------------------------------------------
    // Print graph data for one component to use in isogeny-graphs.ipynb
    // Paste the output into the notebook to produce figures like Figure 1.1.
    // ---------------------------------------------------------------

    C := comps[1];
    Pi_C := RestrictPartition(G2, C, Pi2);
    PrintIsogenyGraphForSage(G2, C, Pi_C);

/*
Expected output (F3 graph):
  Number of vertices: 14
  Number of edges: 18

Expected output (F9 graph):
  Number of vertices (F9): 1763
  Number of isomorphism classes of components: 4
  Component sizes (vertices, count):
    [ <17, 9>, <32, 12>, <49, 2>, <94, 12> ]
*/
