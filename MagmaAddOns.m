Z:=Integers();
Q:=Rationals();

////////////////////
// Isogeny Graph High-Level API
////////////////////

intrinsic PartitionByEndomorphismRing(vert::SeqEnum, R::AlgEtQOrd) -> SeqEnum
{Given the vertex sequence vert returned by IsogenyGraphBuilder and the Frobenius order R,
returns a partition of the vertex indices 1..#vert by endomorphism ring.
Each cell of the partition is a sorted sequence of vertex indices sharing the same
endomorphism ring (MultiplicatorRing). The order of the cells is not significant
(downstream consumers re-sort by cell size).}
    oo    := OverOrders(R);
    cells := AssociativeArray();
    for i in [1..#vert] do
        v  := vert[i];
        // When weak_equivalence:=true, vert[i] is a bare AlgEtQWECMElt;
        // otherwise it is a [* W, L *] pair and the WE class is the first entry.
        OI := Type(v) eq List select MultiplicatorRing(v[1])
                                else MultiplicatorRing(v);
        j  := Index(oo, OI);
        if IsDefined(cells, j) then
            Append(~cells[j], i);
        else
            cells[j] := [i];
        end if;
    end for;
    // The per-cell Sort below is meaningful (vertex indices within a cell).
    // We deliberately do not sort the sequence of cells: that lex order of
    // sorted index-lists carries no level/endomorphism-ring semantics, and
    // downstream code re-sorts the cells by size anyway.
    Pi := [Sort(cells[j]) : j in Keys(cells)];
    return Pi;
end intrinsic;

intrinsic RestrictPartition(G::GrphMult, G0::GrphMult, Pi::SeqEnum) -> SeqEnum
{Given the full isogeny graph G, a connected component G0, and a partition Pi of vertex
indices in G (as returned by PartitionByEndomorphismRing), returns the restriction of Pi
to the vertices of G0. Empty cells are dropped.}
    V      := Vertices(G);
    verts0 := {Index(V!v) : v in Vertices(G0)};
    Pi0    := [Sort([i : i in cell | i in verts0]) : cell in Pi];
    return [cell : cell in Pi0 | #cell gt 0];
end intrinsic;

intrinsic ComputeIsogenyGraph(h::RngUPolElt, D::RngIntElt : use_orbits:=false, weak_equivalence:=false) -> GrphMultDir, SeqEnum, Assoc, SeqEnum
{Given a Weil polynomial h and a positive integer D, computes the D-isogeny graph of the
corresponding ordinary isogeny class. Returns:
  G    -- the D-isogeny graph as a directed multigraph (GrphMultDir)
  verts -- sequence indexing the vertices, whose shape depends on the mode. By default (weak_equivalence false) each entry is a pair [*W,L*], where W is a weak equivalence class (AlgEtQWECMElt) and L is an element of an abstract group representing Pic(T) with T the multiplicator ring of W, as returned by IsogenyGraphBuilder. When weak_equivalence is true each entry is instead a bare weak equivalence class W, as returned by ConstructOrbitGrphMultDir.
  edges -- an associative array, indexed by degrees d dividing D. The value at d will be a sequence of 5-tuples <source, target, Is, It, x>.  source and target will be vertices; Is and It ideals in the source and target; and x*Is subset It is an inclusion of index d representing the isogeny.  If weak_equivalence is false, all edges in the isogeny graph will be included.  If true, then only one edge per G_(S,T) orbit will be included, where S is the multiplicator ring of the source and T the multiplicator ring of the target.
  Pi   -- partition of vertex indices 1..#verts by endomorphism ring; a sequence of sequences
          of vertex indices, one per endomorphism ring, sorted lexicographically
To plot a component C of G, call RestrictPartition(G, C, Pi) then PrintIsogenyGraphForSage,
and feed the printed output into plot_isogeny_graph.sage (see README).}
    g, q, p := Getgqp(h);
    K    := EtaleAlgebra(h);
    pi   := PrimitiveElement(K);
    R    := Order([pi, q/pi]);
    if weak_equivalence then
        use_orbits := true;
    end if;
    if use_orbits then
        reps := IsogenyOrbitBuilder(R, D);
        if weak_equivalence then
            G, verts, edges := ConstructOrbitGrphMultDir(R, reps);
        else
            verts, edges := IsogenyGraphBuilder_FromOrbit(R, D, reps);
        end if;
    else
        verts, edges := IsogenyGraphBuilder(R, D);
    end if;
    if not assigned G then
        G := ConstructStandardGrphMultDir(verts, edges);
    end if;
    Pi := PartitionByEndomorphismRing(verts, R);
    return G, verts, edges, Pi;
end intrinsic;

intrinsic PrintIsogenyGraphForSage(G::GrphMult, G0::GrphMult, Pi0::SeqEnum : Pi_global:=[])
{Prints edge list and vertex partition for the component G0 of the isogeny graph G,
using global vertex indices from G. Feed the printed output into plot_isogeny_graph.sage
to produce the figure (see README for the pipeline).
If the optional argument Pi_global (the partition of the whole graph G, as returned by
ComputeIsogenyGraph) is supplied, the global_num_levels and global_level_indices lines
that the figure pipeline relies on for cross-component color consistency are also emitted,
so a stand-alone single-component render matches the colors of a pipeline render.}
    V         := Vertices(G);
    E0        := Edges(G0);
    num_edges := #E0;
    // Always emit the edge list as edges=[ ... ] (the empty case is edges=[] too),
    // so the output shape is identical whether or not the component has edges.
    if num_edges eq 0 then
        print "edges=[]";
    else
        "edges=[";
        for i in [1..num_edges-1] do
            e := E0[i];
            printf "%o,", [Index(V!InitialVertex(e)), Index(V!TerminalVertex(e))];
        end for;
        e0 := E0[num_edges];
        printf "%o]\n", [Index(V!InitialVertex(e0)), Index(V!TerminalVertex(e0))];
    end if;
    printf "Pi=%o\n", Pi0;
    if #Pi_global gt 0 then
        // 0-indexed position of each Pi0 cell within Pi_global, matching the
        // global_* lines emitted by magma_gen_all_plots.m's PrintSection.
        level_indices := [];
        for cell in Pi0 do
            v := cell[1];
            Append(~level_indices, [i - 1 : i in [1..#Pi_global] | v in Pi_global[i]][1]);
        end for;
        printf "global_num_levels=%o\n", #Pi_global;
        printf "global_level_indices=%o\n", level_indices;
    end if;
end intrinsic;

////////////////////
// Weil Polynomial Intrinsics
////////////////////

function Base26Encode(n)
        alphabet := "abcdefghijklmnopqrstuvwxyz";
        s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
        while n gt 0 do
                s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
        end while;
        return s;
end function;


intrinsic IsogenyLabel(f::RngUPolElt)->MonStgElt
{returns the LMFDB label of the isogeny class determined by a Weil polynomial f.}
    g:=Degree(f) div 2;
    q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
    str1:=Reverse(Prune(Coefficients(f)))[1..g];
    str2:="";
    for a in str1 do
        if a lt 0 then
            str2:=str2 cat "a" cat Base26Encode(-a) cat "_";
            else
            str2:=str2 cat Base26Encode(a) cat "_";
        end if;
    end for;
    str2:=Prune(str2);
    isog_label:=Sprintf("%o.%o.",g,q) cat str2;
    return isog_label;
end intrinsic;


intrinsic WeilPolynomial(L:RngUPolElt)->RngUPolElt
{Convert an L-polynomial of an abelian variety to an P-polynomial (characteristic polynomial of the Frobenius). It does no testing.}
    P:=Parent(L);
    x:=P.1;
    g:=Z!(Degree(L)/2);
    f:=P!(x^(2*g)*Evaluate(L,1/x));
    return f;
end intrinsic;

intrinsic Getgqp(f::RngUPolElt)->RngIntElt,RngIntElt,RngIntElt
{Given a Weil polynomial of an abelian variety determine the g, the dimension, q, cardinality of the base field, p, the characteristic of the base field.
This does no testing if the element f is actually a Weil polynomial.}
    bool,p,r:=IsPrimePower(ConstantCoefficient(f));
    g:=Z!(Degree(f)/2);
    s:=Z!(r/g);
    q:=p^s;
    return g,q,p;
end intrinsic;

intrinsic WeilBaseChange(f::RngUPolElt,r::RngIntElt)->RngUPolElt
{Given a Weil polynomial over an abelian variety over a finite field with q elements and an integer r compute the Weil polynomial of the abelian variety of the abelian variety base changed to the field with q^r elements.}
    P:=Parent(f);
    x:=P.1;
    P1<y,u>:=PolynomialRing(Z,2);
    ff:=Evaluate(f,u);
    f2:=Resultant(u^r-y,ff,u);
    f2:=P!Evaluate(f2,[x,0]);
    return f2;
end intrinsic;

