declare attributes AlgEtQOrd:UnitsModTotPos,
                             TotPosUnitsModUbarU,
                             BarInversePic;

declare attributes AlgEtQWECMElt:DualWKClasses;

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

intrinsic DualWKClasses(w::AlgEtQWECMElt)->AlgEtQWECMElt,.
{Returns the AlEtQWEElt wtbar corresponding to Wtbar:=TraceDualIdeal(ComplexConjugate(Ideal(w))) and the invertible ideal class of the colon ideal (Wtbar,Ideal(wtbar)) as an element of Pic. Data is stored in an attribute populated on demand.}
    if not assigned w`DualWKClasses then
        W_map:=RepresentativeMap(Parent(w));
        Wtbar:=TraceDualIdeal(ComplexConjugate(Ideal(w)));
        wtbar:=Wtbar@@W_map;
        Sb:=MultiplicatorRing(wtbar);
        _,pSb:=PicardGroup(Sb);
        jj:=(Sb!!ColonIdeal(Wtbar,Ideal(wtbar)))@@pSb;
        w`DualWKClasses:=<wtbar,jj>;
    end if;
    return Explode(w`DualWKClasses);
end intrinsic;

function dual_vertex(w,aa)
// given a weak equivalence class w (of type AlgEtQWECMElt), with multiplictor ring T and element aa of the abstract group representing Pic(T), say representing the ideal class of the fractioanl ideal I,  it returns wt,aat representing the ideal class of TraceDualIdeal(ComplexConjugate(I)).
    // We have the relation \bar{I*L)^t = \bar{I}^t * \bar{L}^-1
    S:=MultiplicatorRing(w);
    W:=Parent(w);
    W_map:=RepresentativeMap(W);
    wtbar,jj:=DualWKClasses(w);
    aat:=BarInversePic(S)(aa);
    return wtbar,jj*aat;
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

intrinsic DualIsogenies_FromIter(R::AlgEtQOrd, D::RngIntElt : only_square_divisors:=true)->Assoc
{Given the Frobenius order R of an isogeny class of ordinary squarefree abelian varieties over a finite field and an integer D>1, it returns an associative array isog, indexed by divisors d>1 of D where isog[d] is a sequence of isogenies from A to the dual of A, representing all equivalence classes of such isogenies.
tuples of the form < [* w, aa *] , [* wt, aat *], IV , IVdual , x > where
- IV is the distinguished representative of the ideal class [* w , aa *];
- IVdual = ComplexConjugate(TraceDualIdeal(IV));
- [* wt , aat *] is the ideal class of the dual vertex
- x*IV < IVdual is an inclusion of degree d.
Note that IVdual might not be the distinguished representative of [* wt , aat *].
The vararg only_square_divisors (default true) determines if d in the output must be a square.
The intrinsic calls internally IsogenyGraphBuilder.}
    classes,edges:=IsogenyGraphBuilder(R,D);
    ans := AssociativeArray();
    for vertex in classes do
        w,aa:=Explode(vertex);
        IV:=DistinguishedRepsICM(w,aa);
        wt,aat:=dual_vertex(w,aa);
        IVv:=DistinguishedRepsICM(wt,aat);
        IVtbar:=ComplexConjugate(TraceDualIdeal(IV));
        test,iota:=IsIsomorphic(IVtbar,IVv); // iota*IVv=\bar(IV^t)
        assert test;
        for d->edges_d in edges do
            if IsSquare(d) or not only_square_divisors then
                if not IsDefined(ans, d) then
                    ans[d] := [];
                end if;
                for E in edges_d do
                    // we check if the source is IV and target is IVv
                    if E[3] eq IV and E[4] eq IVv then 
                        i_x0:=iota*E[5];
                        assert2 E[1] eq vertex and E[2] eq [* wt,aat *];
                        // Note: we include the tuple but changing the label:
                        // instead of x0*IV<IVv we put i*x0*IV<\bar{IV}^t. 
                        Append(~ans[d],< E[1] , E[2], IV, IVtbar , i_x0 >);
                    end if;
                end for;
            end if;
        end for;
    end for;
    return ans;
end intrinsic;

intrinsic NonPrincipalPolarizationsOfDegreeDividing(R::AlgEtQOrd,PHI::AlgEtQCMType,D::RngIntElt : method:="FromIter")->Assoc
{Given the Frobenius order R of an isogeny class of ordinary squarefree abelian varieties over a finite field, a p-adic positive CM-type PHI, and an integer D>1, it returns an associative array pols, with pols[d] consisting of representatives of isomorphism classes of polarizations of degree d, where d>1 is a divisor of D, given by tuples of the form < [* w, aa *] , [* wt, aat *], IV , IVdual , lambda > where
- IV is the distinguished representative of the ideal class [* w , aa *];
- IVdual = ComplexConjugate(TraceDualIdeal(IV));
- [* wt , aat *] is the ideal class of the dual vertex
- lambda*IV < IVdual is a polarization of degree d.
Note that IVdual might not be the distinguished representative of [* wt , aat *].
The parameter method which can have values "FromIter" or"FromOrbit" determines whether DualIsogenies_FromIter, DualIsogenies_FromOrbit is used.}
    require method in {"FromIter","FromOrbit"} : "the parameter method should equal FromIter or FromOrbit";
    if method eq "FromIter" then
        isogs_to_dual:=DualIsogenies_FromIter(R,D : only_square_divisors:=true );
    else //"FromOrbit"
        isogs_to_dual:=DualIsogenies_FromOrbit(R,D : only_square_divisors:=true );
    end if;
    pols:=AssociativeArray();
    for d->isogs_to_dual_d in isogs_to_dual do
        if not IsDefined(pols,d) then
            pols[d]:=[];
        end if;
        for isog in isogs_to_dual_d do
            V,Vv,IV,IVbart,x:=Explode(isog);
            S:=MultiplicatorRing(IV);
            cS:=UnitsModTotPos(S);
            for v in cS do
                mu:=x*v;
                if is_polarizaton(mu,PHI) then
                    cSp:=TotPosUnitsModUbarU(S);
                    pols[d] cat:=[<V,Vv,IV,IVbart,mu*vv> : vv in cSp];
                    break v; // if v such that mu is tot img and PHI-positive exists, then it is unique
                end if;
            end for;
        end for;
    end for;
    return pols;
end intrinsic;

/* TESTS

    AttachSpec("spec");
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

    SetDebugOnError(true);
    SetAssertions(2);
    SetColumns(0);
    AttachSpec("../AbVarFq/spec"); // adjust to your local clone of github.com/stmar89/AbVarFq
    AttachSpec("spec");
    _<x>:=PolynomialRing(Integers());
    //f:=x^4-2*x^2+121;
    f:=x^4 - 4*x^3 + 11*x^2 - 16*x + 16;
    If:=IsogenyClass(f);
    PHI:=pAdicPosCMType(If);
    R:=ZFVOrder(If);
    Ds:=[2,4,9,25,4*9,9*25,4*9*25];
    for method in ["FromIter"] do
        method;
        for D in Ds do
            t0:=Cputime();
            pols:=NonPrincipalPolarizationsOfDegreeDividing(R,PHI,D : method:=method);
            t1:=Cputime(t0);
            counts:=[];
            for d->pols_d in pols do
                Append(~counts,<d,#pols_d>);
            end for;
            printf "D=%o,\ttime=%o,\tnum. pols. of deg.=%o\n",D,t1,counts;
        end for;
    end for;

*/
