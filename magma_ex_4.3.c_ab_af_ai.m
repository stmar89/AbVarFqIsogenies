/*
    Examples 1.1 and ?

    This example is about the 2-isogenies in the isogeny class 4.3.c_ab_af_ai of abelian varieties over F3, i
    and of its extension to F9.

    This code is paired with a sage-notebook for the graphical outputs.
*/

    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");
    _<x>:=PolynomialRing(Integers());
    h:=x^8 + 2*x^7- x^6 - 5*x^5 - 8*x^4 - 15*x^3 - 9*x^2 + 54*x + 81;
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    K:=EtaleAlgebra(h);
    pi:=PrimitiveElement(K);

    // Consider the Frobenius order of the isogeny class
    R:=Order([pi,q/pi]);

    // We compute the 2-isogeny graph.
    D:=2;
    V,ED:=IsogenyGraphBuilder(R,D);
    GD:=ConstructStandardGrphMultDir(V,ED);


    // We compute the 2-isogeny graph of the base field extension to F9
    R2:=Order([pi^2,(q/pi)^2]);
    V2,ED2:=IsogenyGraphBuilder(R2,D);
    GD2:=ConstructStandardGrphMultDir(V2,ED2);
    comps:=[ Component(Random(c)) : c in StronglyConnectedComponents(GD2) ];
    classes:=[];
    for Gc in comps do
        if not exists{G:G in classes|IsIsomorphic(Gc,G)} then // FIXME cannot test IsIsomorphic for MultiDiGraph :-(
            Append(~classes,Gc);
        end if;
    end for;

