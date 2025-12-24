   
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
    h:=1 - 3*x + 5*x^2 - 9*x^3 + 9*x^4;
    //h:=1 - 7*x + 31*x^2;
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

