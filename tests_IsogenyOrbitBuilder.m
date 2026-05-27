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
        if #mismatches ne 0 then
            printf "...got issues\n";
        else
            printf "...all good\n";
        end if;
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
