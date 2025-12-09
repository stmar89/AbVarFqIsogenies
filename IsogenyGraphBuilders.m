// the name of the algorithms are not the definitive ones.

declare attributes AlgEtQOrd: QuotientsUnitsOverorders;

intrinsic QuotientsUnitsOverorders(R::AlgEtQOrd,T::AlgEtQOrd,S::AlgEtQOrd)->SeqEnum
{Given an order R and two overorders T,S of R, returns a sequence of representatives in K of T^*/(S^* meet T^*). The output for each ordered pair <T,S> is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`QuotientsUnitsOverorders then
       R`QuotientsUnitsOverorders:=AssociativeArray();
    end if;
    if not IsDefined(R`QuotientsUnitsOverorders,<T,S>) then
        if T subset S then
            // if T < S then T^* < S^*, so the quotient is trivial
            R`QuotientsUnitsOverorders[<T,S>]:=[One(Algebra(R))];
        else
            UT,UTmap:=UnitGroup(T);
            US,USmap:=UnitGroup(S);
            if UT subset US then
                // this choice of transversal might make things faster later
                R`QuotientsUnitsOverorders[<T,S>]:=[One(Algebra(R))];
            else
                R`QuotientsUnitsOverorders[<T,S>]:=[UTmap(v):v in Transversal(UT,UT meet US)];
            end if;
        end if;
    end if;
    return R`QuotientsUnitsOverorders[<T,S>];
end intrinsic;

compute_orbits_UT_on_Ms:=function(T,Ms,R)
// Input: Ms a sequence of fractional R-ideals, all contained in a fractional ideal J, with multiplicator ring T, 
// where T is an overorder of R, and such that T^* acts on Ms, that is, for u in T^* and M in Ms, u*M is in Ms.
// Output: a sequence of elements of Ms, representing the distinct orbits of the action of T^* on Ms.
    remaining:={@ M:M in Ms @};
    orbits:=[];
    repeat
        M1:=remaining[1];
        Append(~orbits,M1);
        // We compute the orbit of M1:
        // If S is the multiplicator ring of M1, then S^* acts trivially on M1.
        // So, the orbit of M1 by the action of T^* can be computed using the finite quotient T^*/(S^* meet T^*)
        // Reps in K of this quotient are stored in the associative array R`QuotientsUnitsOverorders[<T,S>], 
        // which is populated on demand by the corresponding intrinsc, to avoid useless recomputation.
        S:=MultiplicatorRing(M1);
        orbit_M1:={@ v*M1:v in QuotientsUnitsOverorders(R,T,S) @};
        remaining diff:=orbit_M1;
    until #remaining eq 0;
    return orbits;
end function;


//TODO details about output
intrinsic IsogenyGraphBuilder_ModuloNothing(R::AlgEtQOrd,N::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the N-isogeny graph.}
    icm,icm_map:=IdealClassMonoidAbstract(R);
    classes:=Classes(icm);
    edges:=[];
    for target in classes do 
        IV:=icm_map(target); //IV is a representative of each vertex, chosen once and for all
        Ms:=[M:M in IntermediateIdeals(IV,N*IV)|N mod Index(IV,M) eq 0]; //sub-frac.R-ideals M<IV s.t. [IV:M]|N
        T:=MultiplicatorRing(IV);
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            source:=icm!M;
            IV1:=icm_map(source); //this is chosen once and for all
            test,x:=IsIsomorphic(M,IV1); //x*IV1 = M 
            assert test; // sanity check
//            assert x*IV1 eq M; //TODO to make sure that the order is correct... I often get confused. remove later
            Append(~edges,<[* WEClass(source),PicClass(source) *],[* WEClass(target),PicClass(target) *],IV1,IV,x>);
        end for;
    end for;
    return [[* WEClass(target),PicClass(target) *]:target in classes],edges;
end intrinsic;

intrinsic IsogenyGraphBuilder_ModuloPic(R::AlgEtQOrd,N::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the N-isogeny graph.}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    classes:=[];
    edges:=[];
    for t in Classes(we) do 
        T:=MultiplicatorRing(t);
        eT:=ExtensionHomPicardGroups(R,T);
        PT:=PicardGroup(T);
        Wt:=we_map(t);
        Ms:=[M:M in IntermediateIdeals(Wt,N*Wt)|N mod Index(Wt,M) eq 0]; //sub-frac.R-ideals M<Wt s.t. [Wt:M]|N
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            source_M:=M@@icm_map;
            s:=WEClass(source_M);
            aaS:=PicClass(source_M);
            S:=MultiplicatorRing(s);
            Ws:=we_map(s);
            eS:=ExtensionHomPicardGroups(R,S);
            aa:=aaS@@eS; // in Pic(R);
            Iaa:=pR(aa);
            test,x:=IsIsomorphic(M,Ws*Iaa);
            assert test; // sanity check
            for bbT in PT do
                Append(~classes,[* t,bbT *]);
                bb:=bbT@@eT;
                Ibb:=pR(bb);
                Append(~edges,<[* s,aaS *],[* t,bbT *],Ws*Iaa*Ibb,Wt*Ibb,x>);
            end for;
        end for;
    end for;
    return classes,edges;
end intrinsic;

/* TESTS
   
    AttachSpec("~/AlgEt/spec");
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");

    _<x>:=PolynomialRing(Integers());
    f:=x^8+16;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    time _:=IsogenyGraphBuilder_ModuloNothing(R,2);


    //SetDebugOnError(true);
    _<x>:=PolynomialRing(Integers());
    f:=x^8+16;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    time _:=IsogenyGraphBuilder_ModuloPic(R,2);



    _:=IsogenyGraphBuilder_ModuloNothing(R,4);
    _:=IsogenyGraphBuilder_ModuloNothing(R,8);
    _:=IsogenyGraphBuilder_ModuloNothing(R,8*27);
    

*/


