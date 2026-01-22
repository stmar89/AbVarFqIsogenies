/*
    Tests for IsogenyOrbitBuilder
*/

    AttachSpec("~/AbVarFqIsogenies/spec");
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
    AttachSpec("~/AbVarFqIsogenies/spec");
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
    AttachSpec("~/AbVarFqIsogenies/spec");
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
