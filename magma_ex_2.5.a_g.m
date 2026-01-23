/*
    Example 3.7

    This example exhibits a descending 2-isogeny A -> B such that the inclusion End(B) < End(A) is not minimal, in the 
    sense that there exists an abelian variety C in the same isogeny class and strict inclusions End(B) < End(C) < End(A).
    This cannot happend for elliptic curves.
*/

    AttachSpec("~/AbVarFqIsogenies/spec");
    PP<x>:=PolynomialRing(Integers());
    SetColumns(0);

    // Consider the isogeny class defined by
    h:=x^4 + 6*x^2 + 25;
    K:=EtaleAlgebra(h);
    OK:=MaximalOrder(K);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    _,p:=IsPrimePower(q);
    V:=q/F;
    R:=Order([F,V]);
    
    // The Frobenius order has index in OK :
    Index(OK,R);

    // We consider the unique overorder S of index 8 in OK.
    oo:=OverOrders(R);
    indices:=[ Index(OK,S) : S in oo ];
    assert #[i:i in indices| i eq 8 ] eq 1;
    S:=oo[Index(indices,8)];
    Index(OK,S);

    // Consider the conductor (S:OK) of S in OK
    fS:=Conductor(S);

    // The inclusion fS < S induces an isogeny of degree:
    Index(S,fS);

    // The isogeny is minimal since fS is the unique singular maximal ideal of S:
    [ fS ] eq SingularPrimes(S);
    // which has index 2 in S:
    Index(S,fS);

    // The isogeny is descending since the multiplicator ring of fS is OK.
    MultiplicatorRing(fS) eq OK;

    // The inclusion S < OK is not minimal: there are several orders in between:
    #[T:T in oo | T ne S and T ne OK and S subset T and T subset OK ];
