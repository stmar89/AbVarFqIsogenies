/*
    Example 3.10

    This example is about the 2-isogenies in the isogeny class 2.11.a_ac of abelian surfaces over F11.
    We show that there exists an abelian surface A with endomorphism ring S_4 of index 4 in the maximal
    order of the endomorphism algebra with a horizontal 2-isogeny B->A.
    This cannot happen for elliptic curves.
*/

    // Run from the AbVarFqIsogenies/ directory
    AttachSpec("spec");
    _<x>:=PolynomialRing(Integers());
    h:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    K:=EtaleAlgebra(h);
    pi:=PrimitiveElement(K);

    // Consider the Frobenius order of the isogeny class
    R:=Order([pi,q/pi]);
    // and its overorders.
    oo:=OverOrders(R);
    OK:=MaximalOrder(K);
    [ Index(OK,S) : S in oo ];
    // R has a unique singular maximal ideal, with norm 2
    [ Index(R,P) : P in SingularPrimes(R) ];
    P:=SingularPrimes(R)[1];

    // Consider the trace dual ideal J of the overorder S4 of R which has index 4 in OK.
    // Note that J has multiplicator ring S4.
    S4:=oo[2];
    assert Index(OK,S4) eq 4;
    J:=R!!TraceDualIdeal(S4);
    OJ:=MultiplicatorRing(J);
    assert OJ eq S4;

    // We compute the 2-isogenies with target J, by listing the sub-R-ideals M < J of index 2
    MM:=SubIdealsOfIndexDividing(J,2);
    // We get 3 isogenies, which we now study:
    hor:=[];
    desc:=[];
    for M in MM do
        OM:=MultiplicatorRing(M);
        assert P*J subset M;
        if OM eq OJ then
            "horizontal";
            Append(~hor,M);
        elif OM subset OJ then
            Index(OK,OM),"ascending",Index(OJ,OM);
        elif OJ subset OM then
            Index(OK,OM),"descending",Index(OM,OJ);
            Append(~desc,M);
        else
            Index(OK,OM),"not contained";
        end if;
    end for;

    // So we get one descending isogeny and two horizontal ones.
    // For the descending isogeny, we have that M equals the trace dual ideal of the order S2 of index 2 in OK:
    M:=desc[1];
    S2:=oo[3];
    assert Index(OK,S2) eq 2;
    M eq R!!TraceDualIdeal(S2);

    // For the horizontal isogenies, the source are invertible S4-ideals.
    for I in hor do
        MultiplicatorRing(I) eq S4;
        IsInvertible(S4!!I);
    end for;
    // The two isogenies are not equivalent, that is, they give rise to discinct edges in the 2-isogeny graph.
    AreIsogeniesEquivalent(K!1,hor[1],J,K!1,hor[2],J);

/*
Expected output:

  [ 8, 4, 2, 1 ]                  -- indices of overorders in OK: R, S4, S2, OK
  [ 2 ]                           -- R has a unique singular prime of norm 2
  horizontal
  2 descending 2
  horizontal
  true                            -- M eq TraceDualIdeal(S2)
  true                            -- MultiplicatorRing(hor[1]) eq S4
  true                            -- IsInvertible(S4!!hor[1])
  true                            -- MultiplicatorRing(hor[2]) eq S4
  true                            -- IsInvertible(S4!!hor[2])
  false                           -- the two horizontal isogenies are not equivalent
*/

