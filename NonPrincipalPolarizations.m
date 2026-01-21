declare attributes AlgEtQOrd:UnitsModTotPos,
                             TotPosUnitsModUbarU,
                             BarInversePic;

intrinsic UnitsModTotPos(S::AlgEtQOrd)->SeqEnum[AlgEtQElt]
{Given an order S in a CM-etale algebra K returns a set of representative in K of the quotient S^*/S_+^*, where S_+^* is the subgroup of totally real totally positive units of S.}
    if not assigned S`UnitsModTotPos then
        U,u:=UnitGroup(S);
        Up:=TotallyRealPositiveUnitGroup(S);
        S`UnitsModTotPos:=[u(v):v in Transversal(U,Up)];
    end if;
    return S`UnitsModTotPos;
end intrinsic;

intrinsic TotPosUnitsModUbarU(S::AlgEtQOrd)->SeqEnum[AlgEtQElt]
{Given an order S in a CM-etale algebra K returns a set of representative in K of the quotient S_+^*/(S^* meet <u*\bar(u): u in S^*>, where S_+^* is the subgroup of totally real totally positive units of S.}
    if not assigned S`TotPosUnitsModUbarU then
        U,u:=UnitGroup(S);
        Up:=TotallyRealPositiveUnitGroup(S);
        if IsConjugateStable(S) then
            gens:=[Up!(U.i*ComplexConjugate(u(U.i))@@u): i in [1..Ngens(U)]];
            den:=sub<Up|gens>;
        else
            UK,uK:=UnitGroup(MaximalOrder(Algebra(S)));
            gens_inUK:=[(UK!(U.i)*(ComplexConjugate(u(U.i))@@uK)): i in [1..Ngens(U)]];
            den:=Up meet sub<UK|gens_inUK>;
        end if;
        trans:=Transversal(Up,den);
        S`TotPosUnitsModUbarU:=[u(t):t in trans];
    end if;
    return S`TotPosUnitsModUbarU;
end intrinsic;

intrinsic BarInversePic(S::AlgEtQOrd)->Map
{Given an order S in a CM-etale algebra returns the group homomorphism PS->PSb where PS=PicardGroup(S) and PSb:=PicardGroup(ComplexConjugate(S)) induced by L:->ComplexConjugate(Inverse(L)).}
    if not assigned S`BarInversePic then
        Sb:=ComplexConjugate(S);
        PS,pS:=PicardGroup(S);
        PSb,pSb:=PicardGroup(Sb);
        output:=hom<PS->PSb|[(ComplexConjugate(pS(-PS.i)))@@pSb : i in [1..Ngens(PS)]]>;
        S`BarInversePic:=output;
    end if;
    return S`BarInversePic;
end intrinsic;

function dual_vertex(w,aa)
// given a weak equivalence class w (of type AlgEtQWECMElt), with multiplictor ring T and element aa of the abstract group representing Pic(T), say representing the ideal class of the fractioanl ideal I,  it returns wt,aat representing the ideal class of TraceDualIdeal(ComplexConjugate(I)).
    // We have the relation \bar{I*L)^t = \bar{I}^t * \bar{L}^-1
    S:=MultiplicatorRing(w);
    W:=Parent(w);
    W_map:=RepresentativeMap(W);
    wt:=TraceDualIdeal(ComplexConjugate(Ideal(w)))@@W_map;
    return wt,BarInversePic(S)(aa);
end function;

function is_polarizaton(mu,PHI)
    if mu eq -ComplexConjugate(mu) //totally imaginary
        and forall{phi:phi in Homs(PHI)| Im(phi(mu)) gt 0} // PHI-positive
            then
        return true;
    else
        return false;
    end if;
end function;

intrinsic NonPrincipalPolarizationsOfDegreeDividing(R::AlgEtQOrd,PHI::AlgEtQCMType,D::RngIntElt)->SeqEnum
{Given the Frobenius order R of an isogeny class of ordinary squarefree abelian varieties over a finite field, a p-adic positive CM-type PHI, and an integer D>1, it returns an associative array pols, indexed by divisors d>1 of D where pols[d] is an associative array indexed by fractional R-ideals I, representing the ideal class monoid of R, and pols[d][I] is a sequence of elements x in Q[F] each one representing a polarization of I of degree d (necesarily a sqare) up to polarized isomorphism. If no such polarization is found, an empty sequence is stored.
The intrinsic calls internally IsogenyGraphBuilder.}
    classes,edges:=IsogenyGraphBuilder(R,D);
    pols:=AssociativeArray();
    for vertex in classes do
        w,aa:=Explode(vertex);
        IV:=DistinguishedRepsICM(w,aa); // IV is the same as I in the description.
        S:=MultiplicatorRing(w);
        cS:=UnitsModTotPos(S);
        cSp:=TotPosUnitsModUbarU(S);
        wt,aat:=dual_vertex(w,aa);
        IVv:=DistinguishedRepsICM(wt,aat);
        test,i:=IsIsomorphic(ComplexConjugate(TraceDualIdeal(IV)),IVv); // i*IVv=\bar(IV^t)
        assert test;
        for d->edges_d in edges do
            if IsSquare(d) then // polarizations have always square degree
                if not IsDefined(pols,d) then
                    pols[d]:=AssociativeArray();
                end if;
                pols_d_IV:=[];
                isog_d_IV:=[ E[5] : E in edges_d | E[3] eq IV and E[4] eq IVv ];
                for x0 in isog_d_IV, v in cS do
                    mu:=i*x0*v;
                    if is_polarizaton(mu,PHI) then
                        pols_d_IV cat:= [mu*vv: vv in cSp];
                    end if;
                end for;
                pols[d][IV]:=pols_d_IV;
            end if;
        end for;
    end for;
    return pols; 
end intrinsic;

/* TESTS

    Attach("~/AbVarFq_Isogenies_Private/magma/NonPrincipalPolarizations.m");
    _<x>:=PolynomialRing(Integers());
    f:=x^8+16; //not ordinary, but it has non-conjugate stable overorders
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    oo:=OverOrders(R);
    assert exists{S:S in oo| not IsConjugateStable(S)};
    for S in oo do
        _:=UnitsModTotPos(S);
        _:=TotPosUnitsModUbarU(S);
    end for;

  
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    Attach("~/AbVarFq_Isogenies_Private/magma/NonPrincipalPolarizations.m");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    If:=IsogenyClass(f);
    PHI:=pAdicPosCMType(If);
    R:=ZFVOrder(If);
    Ds:=[2,4,9,25,4*9,9*25,4*9*25];
    for D in Ds do
        t0:=Cputime();
        pols:=NonPrincipalPolarizationsOfDegreeDividing(R,PHI,D);
        t1:=Cputime(t0);
        counts:=[];
        for d->pols_d in pols do
            counts_d:=0;
            for I->pols_d_I in pols[d] do
                counts_d+:=#pols_d_I;
            end for;
            Append(~counts,<d,counts_d>);
        end for;
        printf "D=%o,\ttime=%o,\tnum. pols. of deg.=%o\n",D,t1,counts;
    end for;

*/
