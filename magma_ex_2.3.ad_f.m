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

    // Run from the AbVarFqIsogenies/ directory
    AttachSpec("spec");
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
        if i le 11 then
            // if the computation of the icm becomes too expensive, change 11 to a lower number in the previous line
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

/*
Expected output:

i=1	#icm=         1	[Ri:P]=[ 16 ]	[R:Ri]_new=                   1	[R:Ri]_old=                   1
i=2	#icm=         5	[Ri:P]=[ 16 ]	[R:Ri]_new=                 3^2	[R:Ri]_old=                   1
i=3	#icm=        25	[Ri:P]=[ 16 ]	[R:Ri]_new=                  23	[R:Ri]_old=                   1
i=4	#icm=       145	[Ri:P]=[ 16 ]	[R:Ri]_new=                  29	[R:Ri]_old=                 3^2
i=5	#icm=      5246	[Ri:P]=[ 2 ]	[R:Ri]_new=              2^6*61	[R:Ri]_old=                   1
i=6	#icm=      8075	[Ri:P]=[ 16 ]	[R:Ri]_new=              3^2*17	[R:Ri]_old=              3^2*23
i=7	#icm=    201707	[Ri:P]=[ 16 ]	[R:Ri]_new=           29^2*1667	[R:Ri]_old=                   1
i=8	#icm=    672945	[Ri:P]=[ 16 ]	[R:Ri]_new=            23^2*103	[R:Ri]_old=              3^2*29
i=9	#icm=    234025	[Ri:P]=[ 16 ]	[R:Ri]_new=            17^2*251	[R:Ri]_old=                  23
i=10	#icm=  10677440	[Ri:P]=[ 2 ]	[R:Ri]_new=                 2^8	[R:Ri]_old=          2^6*3^2*61
i=11	#icm=  10716555	[Ri:P]=[ 16 ]	[R:Ri]_new=         419^2*25453	[R:Ri]_old=                   1
i=12	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=             23*61^2	[R:Ri]_old=        3^4*17*23*29
i=13	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=        5^2*13^6*131	[R:Ri]_old=                   1
i=14	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=                2731	[R:Ri]_old=       3^2*29^2*1667
i=15	#icm=         -	[Ri:P]=[ 2 ]	[R:Ri]_new=           569^2*719	[R:Ri]_old=           2^6*23*61
i=16	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=               15473	[R:Ri]_old=     3^2*23^2*29*103
i=17	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=     9283^2*10449287	[R:Ri]_old=                   1
i=18	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=        3^2*17^4*179	[R:Ri]_old=     3^4*17^2*23*251
i=19	#icm=         -	[Ri:P]=[ 16 ]	[R:Ri]_new=   191*1901^2*276337	[R:Ri]_old=                   1
i=20	#icm=         -	[Ri:P]=[ 2 ]	[R:Ri]_new=      2^6*199^2*1301	[R:Ri]_old=      2^14*3^2*29*61
*/
