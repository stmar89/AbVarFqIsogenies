   
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
        printf "i=%o\tnorms_Ps_above 2=%o\t[R1:Ri]=%o\n",i, [ Index(Ri,P) : P in PrimesAbove(2*Ri) ],pretty_fac_Z(Index(Ris[1],Ri)); 
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




