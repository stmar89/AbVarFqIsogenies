Z:=Integers();
Q:=Rationals();

////////////////////
// Isogeny Graph High-Level API
////////////////////

intrinsic PartitionByEndomorphismRing(vert::SeqEnum, R::AlgEtQOrd) -> SeqEnum
{Given the vertex sequence vert returned by IsogenyGraphBuilder and the Frobenius order R,
returns a partition of the vertex indices 1..#vert by endomorphism ring.
Each cell of the partition is a sorted sequence of vertex indices sharing the same
endomorphism ring (MultiplicatorRing). Cells are sorted lexicographically.}
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
    Pi := [Sort(cells[j]) : j in Keys(cells)];
    Sort(~Pi);
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

intrinsic ComputeIsogenyGraph(h::RngUPolElt, D::RngIntElt : use_orbits:=false, weak_equivalence:=false) -> GrphMult, SeqEnum, Assoc, SeqEnum
{Given a Weil polynomial h and a positive integer D, computes the D-isogeny graph of the
corresponding ordinary isogeny class. Returns:
  G    -- the D-isogeny graph as a directed multigraph (GrphMult)
  verts -- sequence of fractional R-ideals indexing vertices, as returned by IsogenyGraphBuilder, or by ConstructOrbitGrphMultDir (if weak_equivalence is true).  If weak_equivalence is false, then vertices will be pairs [*W,L*] where W is a weak equivalence class and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W.  If weak_equivalence is true, then vertices will just be W.
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

intrinsic PrintIsogenyGraphForSage(G::GrphMult, G0::GrphMult, Pi0::SeqEnum)
{Prints edge list and vertex partition for the component G0 of the isogeny graph G,
using global vertex indices from G. Feed the printed output into plot_isogeny_graph.sage
to produce the figure (see README for the pipeline).}
    V         := Vertices(G);
    E0        := Edges(G0);
    num_edges := #E0;
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

