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
    // with Profiler
    SetProfile(true);
    _:=IsogenyOrbitBuilder(R,6);
    SetProfile(false);
    G:=ProfileGraph();
    ProfilePrintByTotalTime(G:Max:=20);

