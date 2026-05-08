/*
    Example 4.5

    This example is about the 2-isogenies in the isogeny class 2.3.ad_f of abelian surfaces over F3.
    While there is no such isogeny over F3, they do appear after finite field extensions of specific degrees.

*/

    pretty_fac_Z:=function(n)
        if n eq 1 then
            return "1";
        end if;
        n:=Factorization(n);
        str:=Prune(&cat[n[i,2] eq 1 select Sprintf("%o*",n[i,1]) else Sprintf("%o^%o*",n[i,1],n[i,2]):i in [1..#n]]);
        return str;
    end function;

    AttachSpec("~/AbVarFqIsogenies/spec");
    SetColumns(0);
    _<x>:=PolynomialRing(Integers());
    h:=x^4-3*x^3+5*x^2-9*x+9;
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    K:=EtaleAlgebra(h);
    pi:=PrimitiveElement(K);

    R:=Order([pi,q/pi]);
    // We recover the data in Table 1
    inds:=[];
    for i in [1..20] do
        // Consider the Frobenius order of the extension of the isogeny class to F_q^i
        Ri:=Order([pi^i,(q/pi)^i]);
        if i le 12 then
            // if the computation of the icm becomes too expensive, change 12 to a lower number in the previous line
            icm:=#Classes(IdealClassMonoidAbstract(Ri));
            icm:=IntegerToString(icm);
        else
            icm:="-";
        end if;
        // We compute the norm of the maximal ideals above 2
        pp:=[ Index(Ri,M) : M in PrimesAbove(2*Ri) ];
        ind:=Index(R,Ri);
        Append(~inds,ind);
        seq:=[inds[j] : j in [1..i-1] | i mod j eq 0 ];
        if #seq eq 0 then
            ind_new:=ind;
        else
            ind_new:=ind div LCM(seq);
        end if;
        ind_old:=ind div ind_new;
        printf "i=%o\t\#icm=%10o\t[Ri:P]=%o\t[R:Ri]_new=%20o\t[R:Ri]_old=%20o\n",
                i,icm,pp,pretty_fac_Z(ind_new),pretty_fac_Z(ind_old);
    end for;

