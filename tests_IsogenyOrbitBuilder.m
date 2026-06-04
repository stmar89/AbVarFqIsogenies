/*
    Tests for IsogenyOrbitBuilder
*/

    // Run from the AbVarFqIsogenies/ directory
    AttachSpec("spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);

    for D in [2,3,4,6,8,9] do
        printf "D=%o\t",D;
        mismatches:=IsogenyGraphChecker(R,D);
        if #mismatches gt 0 then
            printf "...got issues\n%o\n", mismatches;
        else
            printf "...all good\n";
        end if;
        assert #mismatches eq 0;
    end for;

    // profiling
    AttachSpec("spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    //time _:=IsogenyOrbitBuilder(R,8);


    // with Profiler
    SetProfile(true);
    _:=IsogenyOrbitBuilder(R,8);
    SetProfile(false);
    G:=ProfileGraph();
    ProfilePrintByTotalTime(G:Max:=20);
    // ProfilePrintChildrenByTime(G,684:Max:=20);
    // ProfilePrintChildrenByTime(G,2:Max:=20);

    //timings
    AttachSpec("spec");
    _<x>:=PolynomialRing(Integers());

    for D in [2,3,4,6,8,9] do
        D;
        f:=x^4-2*x^2+121;
        q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
        K:=EtaleAlgebra(f);
        F:=PrimitiveElement(K);
        V:=q/F;
        R:=Order([F,V]);
        time _:=IsogenyGraphBuilder(R,D);

        f:=x^4-2*x^2+121;
        q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
        K:=EtaleAlgebra(f);
        F:=PrimitiveElement(K);
        V:=q/F;
        R:=Order([F,V]);
        time _:=IsogenyOrbitBuilder(R,D);
    end for;

    // Regression: OrbitBuilder empty-Ms branch used to return 0 instead of [].
    SetClassGroupBounds("GRH");
    AttachSpec("spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^4 - 10*x^3 + 36*x^2 - 1010*x + 10201;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    _:=IsogenyOrbitBuilder(R, 9); // would error on the broken code
    printf "regression D=9 on %o: ok\n", f;

    // Testing orbit method vs non-orbit method
    AttachSpec("spec");
    _<x> := PolynomialRing(Integers());
    h := x^8 + 2*x^7 - x^6 - 5*x^5 - 8*x^4 - 15*x^3 - 9*x^2 + 54*x + 81;
    D := 2;
    K:=EtaleAlgebra(h);
    pi:=PrimitiveElement(K);
    g,q,p:=Getgqp(h);
    R:=Order([pi,q/pi]);
    OK:=MaximalOrder(K);
    V,E:=IsogenyGraphBuilder(R,D);
    reps:=IsogenyOrbitBuilder(R,D);
    VV,EE:=IsogenyGraphBuilder_FromOrbit(R,D,reps);
    E:=E[2];
    EE:=EE[2];

    for e in EE do
        assert #[ee:ee in E|AreIsogeniesEquivalent(ee[5],ee[3],ee[4],e[5],e[3],e[4])] eq 1;
    end for;

    for ie->e in E do
        test:=#[ee:ee in EE|AreIsogeniesEquivalent(ee[5],ee[3],ee[4],e[5],e[3],e[4])];
        assert test eq 1;
    end for;

    // B3: orbit-vs-non-orbit at a COMPOSITE degree, so the composition loop body
    // in IsogenyOrbitBuilder actually runs (D=2 above only has minimal edges).
    // Here D=4 has degree-4 edges built as compositions of two degree-2 edges,
    // and we cross-check every degree's edge set, not just one.
    AttachSpec("spec");
    _<x> := PolynomialRing(Integers());
    h := x^4-2*x^2+121;
    D := 4;
    K:=EtaleAlgebra(h);
    pi:=PrimitiveElement(K);
    g,q,p:=Getgqp(h);
    R:=Order([pi,q/pi]);
    V,E:=IsogenyGraphBuilder(R,D);
    reps:=IsogenyOrbitBuilder(R,D);
    VV,EE:=IsogenyGraphBuilder_FromOrbit(R,D,reps);
    assert Keys(E) eq Keys(EE);
    assert exists{d : d in Keys(E) | d gt 2}; // the composition really produced higher-degree edges
    for d->Ed in E do
        EEd := EE[d];
        assert #Ed eq #EEd;
        for e in EEd do
            assert #[ee:ee in Ed|AreIsogeniesEquivalent(ee[5],ee[3],ee[4],e[5],e[3],e[4])] eq 1;
        end for;
        for e in Ed do
            assert #[ee:ee in EEd|AreIsogeniesEquivalent(ee[5],ee[3],ee[4],e[5],e[3],e[4])] eq 1;
        end for;
    end for;
    printf "B3 composition cross-check (D=4) passed for %o\n", h;

    // B4: smoke test for ComputeIsogenyGraph(h, D : weak_equivalence:=true).
    // This path used to crash (A1: missing R arg to ConstructOrbitGrphMultDir;
    // A2: PartitionByEndomorphismRing indexing a bare WE class). Assert it runs
    // and returns a non-empty partition.
    AttachSpec("spec");
    _<x> := PolynomialRing(Integers());
    h := x^4-2*x^2+121;
    G, verts, edges, Pi := ComputeIsogenyGraph(h, 2 : weak_equivalence:=true);
    assert #verts gt 0;
    assert #Pi gt 0;
    printf "B4 weak_equivalence smoke test passed: #verts=%o, #Pi=%o\n", #verts, #Pi;

    // A3 regression: DualIsogenies_FromOrbit used to undercount dual-isogeny
    // classes vs DualIsogenies_FromIter on Example 3.10 (it produced 12 of the
    // 44 classes of degree 4, dropping every isogeny out of the two WE classes
    // whose conjugate and trace-dual-of-conjugate differ). Both are documented
    // to compute ALL equivalence classes, so the counts must agree.
    AttachSpec("spec");
    _<x> := PolynomialRing(Integers());
    h := x^4-2*x^2+121;
    K:=EtaleAlgebra(h);
    pi:=PrimitiveElement(K);
    g,q,p:=Getgqp(h);
    R:=Order([pi,q/pi]);
    assert #DualIsogenies_FromOrbit(R,4)[4] eq #DualIsogenies_FromIter(R,4)[4];
    printf "A3 regression passed: #DualIsogenies_FromOrbit(R,4)[4]=%o\n", #DualIsogenies_FromOrbit(R,4)[4];
