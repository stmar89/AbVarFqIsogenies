   
    pretty_fac_Z:=function(n)
        if n eq 1 then
            return "1";
        end if;
        n:=Factorization(n);
        str:=Prune(&cat[n[i,2] eq 1 select Sprintf("%o*",n[i,1]) else Sprintf("%o^%o*",n[i,1],n[i,2]):i in [1..#n]]);
        return str;
    end function;

    SetColumns(0);
    PP<x>:=PolynomialRing(Integers());
    h:=1 - 3*x + 5*x^2 - 9*x^3 + 9*x^4; // 2.3.ad_f
    //h:=1 - 7*x + 31*x^2; // 1.31.ah
    h:=PP!Reverse(Coefficients(h));
    K:=EtaleAlgebra(h);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    V:=q/F;
    Ris:=[];
    for i in [1..30] do 
        Ri:=Order([F^i,V^i]); 
        Append(~Ris,Ri);
        icm:=#IdealClassMonoidAbstract(Ri);
        printf "i=%o\t#ICM(Ri)=%o\tnorms_Ps_above 2=%o\t[R1:Ri]=%o\n",i,icm,[ Index(Ri,P) : P in PrimesAbove(2*Ri) ],pretty_fac_Z(Index(Ris[1],Ri)); 
    end for;

    SetColumns(0);
    PP<x>:=PolynomialRing(Integers());
    h:=1+2*x-x^2-5*x^3-8*x^4-15*x^5-9*x^6+54*x^7+81*x^8;
    h:=PP!Reverse(Coefficients(h));
    K:=EtaleAlgebra(h);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    _,p:=IsPrimePower(q);
    V:=q/F;
    Ris:=[];
    for i in [1..30] do 
        Ri:=Order([F^i,V^i]); 
        Index(Ri,Order([F^i])) mod p;
//        Append(~Ris,Ri);
//        printf "i=%o\tnorms_Ps_above 2=%o\t[R1:Ri]=%o\n",i, [ Index(Ri,P) : P in PrimesAbove(2*Ri) ],pretty_fac_Z(Index(Ris[1],Ri)); 
    end for;

    IsMaximal(Ris[1]);

// looking for Frob orders R c K such that [OK:R] is divisible by 2, but R has no ideals of index 2.
    all:=Split(Read("weil_poly_sqfree_ord.txt"));
    PP<x>:=PolynomialRing(Integers());
    for c in all do
        h:=PP!eval(c);
        K:=EtaleAlgebra(h);
        F:=PrimitiveElement(K);
        q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
        _,p:=IsPrimePower(q);
        V:=q/F;
        OK:=MaximalOrder(K);
        R:=Order([F,V]);
        if Index(OK,R) mod 2 eq 0 and #IdealsOfIndex(1*R,2) eq 0 then
            h;
        end if;
    end for;


    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    wk:=WeakEquivalenceClassMonoid(R);
    OK:=MaximalOrder(K);
    Index(OK,R);
    P:=PrimesAbove(2*R)[1];
    for W in wk do
        OW:=MultiplicatorRing(W);
        W_inv:=IsWeakEquivalent(OW,W);
        MM:=SubIdealsOfIndexDividing(W,2);
        for M in MM do
            assert M ne W; // M c W
            OM:=MultiplicatorRing(M);
            is_wk:=IsWeakEquivalent(W,M);
            assert P*W subset M;
            if OM eq OW then
                Index(OK,OW),W_inv,is_wk,"horizontal";
            elif OM subset OW then
                Index(OK,OW),W_inv,is_wk,"ascending",Index(OW,OM);
            elif OW subset OM then
                Index(OK,OW),W_inv,is_wk,"descending",Index(OM,OW);
            else
                Index(OK,OW),W_inv,is_wk,"not contained";
            end if;
        end for;
    end for;
    oo:=OverOrders(R);
    [ Index(OK,S):S in oo ];
    S:=oo[2];
    J:=TraceDualIdeal(S);
    assert not IsInvertible(J);
    MM:=SubIdealsOfIndexDividing(J,2);
    AreIsogeniesEquivalent(K!1,MM[1],J,K!1,MM[2],J);
    AreIsogeniesEquivalent(K!1,MM[2],J,K!1,MM[3],J);
    AreIsogeniesEquivalent(K!1,MM[1],J,K!1,MM[3],J);



    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");
    PP<x>:=PolynomialRing(Integers());
    h:=1+2*x-x^2-5*x^3-8*x^4-15*x^5-9*x^6+54*x^7+81*x^8; //4.3.c_ab_af_ai
    h:=PP!Reverse(Coefficients(h));
    K:=EtaleAlgebra(h);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    _,p:=IsPrimePower(q);
    V:=q/F;
    R:=Order([F,V]);
    [ Index(R,P) : P in SingularPrimes(R) ]; // [2,5,5]
    [ IsInvertible(P): P in PrimesAbove(2*R) ]; // [f,t] 
    wk:=WeakEquivalenceClassMonoid(R);
    P:=SingularPrimes(R)[2]; // above 2
    for W in wk do
        OW:=MultiplicatorRing(W);
        d:=Index(R,P);
        MM:=SubIdealsOfIndexDividing(W,d);
        for M in MM do
            assert M ne W; // M c W
            OM:=MultiplicatorRing(M);
            is_wk:=IsWeakEquivalent(W,M);
            if P*W subset M then // iff M c W is a minimal P-isogeny
                if OM eq OW then
                    is_wk,"horizontal";
                elif OM subset OW then
                    is_wk,"ascending",Index(OW,OM);
                elif OW subset OM then
                    is_wk,"descending",Index(OM,OW);
                else
                    is_wk,"not contained";
                end if;
            end if;
        end for;
    end for;
    
    // extend to F9
    R2:=Order([F^2,V^2]);
    IsBass(R2);
    P:=SingularPrimes(R2)[1];
    assert Index(R2,P) eq 2;
    ooP:=OverOrdersAtPrime(R2,P);
    OK:=MaximalOrder(K);
    [ Index(OK,S):S in ooP ];
    [ IsPrincipal(S!!P):S in ooP ];


