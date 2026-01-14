//
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    all:=Split(Read("weil_poly_sqfree_ord.txt"));
    PP<x>:=PolynomialRing(Integers());
    maxs:=AssociativeArray(:Default:=0);
    for c in all do
        h:=PP!eval(c);
        K:=EtaleAlgebra(h);
        F:=PrimitiveElement(K);
        q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
        _,p:=IsPrimePower(q);
        V:=q/F;
        R:=Order([F,V]);
        oR:=OneIdeal(R);
        OK:=MaximalOrder(K);
        N:=Index(OK,R);
        if N gt 1 then
            g:=Degree(h) div 2;
            lengths:=[];
            wk:=WeakEquivalenceClassMonoid(R);
            for J in wk do
                MM:=_MaximalIntermediateIdeals(J,N*J);
                for I in MM do
                    mm:=PrimesAbove(ColonIdeal(I,J) meet oR); // I<J maximal inclusion => (I:J) is maximal
                    assert #mm eq 1;
                    m:=mm[1];
                    T:=MultiplicatorRing(I);
                    S:=MultiplicatorRing(J);
                    if IsInvertible(m) then
                        assert S eq T;
                    else
                        if not S subset T then
                            assert T subset S;
                            T0:=T;
                            T:=S;
                            S:=T0;
                        end if;
                        // now we have S <= T
                        if not exists{M:M in PrimesAbove(S!!m)|T subset MultiplicatorRing(M)} then
                            h,"T notin (M:M)";
                        end if;
                        if exists{H:H in OverOrders(R)|H ne S and H ne T and S subset H and H subset T} then
                            h,"S<T not minimal";
                        end if;
                        test,len:=IsPowerOf(Index(T,S),Index(R,m));
                        assert test;
                        Append(~lengths,len);
                    end if;
                end for;
            end for;
            max_h:=Max(lengths); 
            if max_h gt maxs[g] then
                maxs[g]:=max_h;
                printf "g=%o\tmax len=%o\th=%o\n",g,max_h,h;
            end if;
        end if;
    end for;

    PP<x>:=PolynomialRing(Integers());
    SetColumns(0);
    //h:=x^4 - 2*x^2 + 9;
    h:=x^4 + 6*x^2 + 25; // max length = 3 > g=2; an inclusion S<T is not minimal
    K:=EtaleAlgebra(h);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    _,p:=IsPrimePower(q);
    V:=q/F;
    R:=Order([F,V]);
    oR:=OneIdeal(R);
    OK:=MaximalOrder(K);
    N:=Index(OK,R);
    oo:=OverOrders(R);
    [Index(OK,S):S in oo];
    maxcm,pos:=Max([CohenMacaulayType(S):S in oo]);
    S:=oo[pos];
    Index(OK,S);
    wkS:=WeakEquivalenceClassesWithPrescribedMultiplicatorRing(S);
    for iJS->JS in wkS do
        J:=R!!JS;
        MM:=_MaximalIntermediateIdeals(J,N*J);
        printf "iJS=%o\t,#MM=%o\n",iJS,#MM;
        for iI->I in MM do
            mm:=PrimesAbove(ColonIdeal(I,J) meet oR); // I<J maximal inclusion => (I:J) meet R is maximal in R
            assert #mm eq 1;
            m:=mm[1];
            m_inv:=IsInvertible(m);
            T:=MultiplicatorRing(I);
            S:=MultiplicatorRing(J);
            assert not m_inv;
            if S eq T then
                dir:="hor";
            else
                if not S subset T then
                    assert T subset S;
                    dir:="asc";
                    T0:=T;
                    T:=S;
                    S:=T0;
                else
                    // (J:J) < (I:I)
                    dir:="desc";
                end if;
            end if;
            // now we have S <= T
            T_in_MM:=exists{M:M in PrimesAbove(S!!m)|T subset MultiplicatorRing(M)};
            min_inclusion:=not exists{H:H in OverOrders(R)|H ne S and H ne T and S subset H and H subset T};
            test,len:=IsPowerOf(Index(T,S),Index(R,m));
            assert test;
            printf "  iI=%o\t%o\tT_in_MM=%o\tmin_inclusion=%o\tlen=%o\n",iI,dir,T_in_MM,min_inclusion,len;
        end for;
    end for;

    // the craziest inclusion is I<J is for iJS=1, iI=3
    J:=R!!wkS[1];
    I:=_MaximalIntermediateIdeals(J,N*J)[3];
    OJ:=S;
    assert MultiplicatorRing(J) eq S;
    OI:=MultiplicatorRing(I);
    S subset OI;
    Index(OI,S);


