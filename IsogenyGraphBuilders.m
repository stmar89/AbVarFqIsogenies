// the name of the algorithms are not the definitive ones.

declare attributes AlgEtQOrd: QuotientsUnitsOverorders, // transversals in K of T^*/(S^* meet T^*)
                              QuotientOfJoinUnitsOverOrders, // transversals in K of O2^*/(O1^*O3^* meet O2^*)
                              InclusionOverorders, // whether S < T
                              JoinUnitsOverorders, // S^*T^* as a subgroup of OK^*
                              KernelsExtensionHoms, // ker(e_S)
                              KernelIntersections, // ker(e_S) meet ker(e_T) as a subgroup of Pic(R)
                              GSTQuotients, // Pic(R) / ker(e_S) meet ker(e_T)
                              DoubleKernelQuotients, // ker(e_T) / ker(e_S) meet ker(e_T)
                              TripleKernelQuotients, // ker(e_T) / (ker(e_T) meet (ker(e_S) + ker(e_U)))
                              DistinguishedRepsICM;

intrinsic DistinguishedRepsICM(w::AlgEtQWECMElt,aa::GrpAbElt)->AlgEtQIdl,AlgEtQIdl,GrpAbElt
{Given w a weak equivalence class of some order R, with multiplicator ring T, and an element aa of the abstract group Pic(T), returns W*I,I,aaR , where W=Ideal(w) and I=pR(aaR) with aaR=aa@@eT, where _,pR:=PicardGroup(R) and eT:=ExtensionHomPicardGroups(R,T). In particular, W*I is canonically associated to the pair (w,aa). The output is stored in the attribute DistinguishedRepsICM of R, and populated on demand.}
    R:=Order(Parent(w));
    if not assigned R`DistinguishedRepsICM then
        R`DistinguishedRepsICM:=AssociativeArray();
    end if;
    if not IsDefined(R`DistinguishedRepsICM,w) then
        R`DistinguishedRepsICM[w]:=AssociativeArray();
    end if;
    if not IsDefined(R`DistinguishedRepsICM[w],aa) then
        T:=MultiplicatorRing(w);
        eT:=ExtensionHomPicardGroups(R,T);
        _,pR:=PicardGroup(R);
        aaR:=aa@@eT;
        IaaR:=pR(aaR);
        R`DistinguishedRepsICM[w][aa]:=<Ideal(w)*IaaR,IaaR,aaR>;
    end if;
    return Explode(R`DistinguishedRepsICM[w][aa]);
end intrinsic;

intrinsic SubIdealsOfIndexDividing(I::AlgEtQIdl,N:RngIntElt)->SetIndx[AlgEtQIdl]
{Given a fractional R-ideal I and a positive integer N, returns all fractional R-ideals J < I such that [I:J] divides N. They are produced recursively from the maximal ones. I is not part of the output.}
    if N eq 1 then
        return {@ I @};
    end if;
    J:=N*I;
    queue:={@ I @};
    output:={@ @};
    done:={@ @};
    while #queue gt 0 do
        pot_new:=&join[_MaximalIntermediateIdeals(elt,J) : elt in queue ];
        pot_new:={@ K : K in pot_new | N mod Index(I,K) eq 0 @}; // we keep only the ones whose index divides N 
        output join:={@ K : K in pot_new | not K in done @};
        done join:=queue;
        queue:=pot_new diff done;
    end while;
    return output;
end intrinsic;

intrinsic QuotientOfJoinUnitsOverOrders(R::AlgEtQOrd, O1::AlgEtQOrd, O2::AlgEtQOrd, O3::AlgEtQOrd)->SeqEnum[AlgEtQElt]
{Let O1,O2,O3 be overorders of R. It returns a transversal of O2^*/(O1^*O3^* meet O2^*). The output is stored in an associative array attribute of R, populated on demand.}
    if not assigned R`QuotientOfJoinUnitsOverOrders then
       R`QuotientOfJoinUnitsOverOrders:=AssociativeArray();
    end if;
    o13:={O1,O3};
    key:=<O2,o13>;
    if not IsDefined(R`QuotientOfJoinUnitsOverOrders,key) then
        U2,u2:=UnitGroup(O2);
        den:=JoinUnitsOverorders(R,O1,O3) meet U2;
        R`QuotientOfJoinUnitsOverOrders[key]:=[u2(t): t in Transversal(U2,den)];
    end if;
    return R`QuotientOfJoinUnitsOverOrders[key];
end intrinsic;

intrinsic JoinUnitsOverorders(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->GrpAb
{Given an order R and two overorders S,T of R, returns S^*T^* as a subgroup of OK^*. The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`JoinUnitsOverorders then
       R`JoinUnitsOverorders:=AssociativeArray();
    end if;
    set:={S,T};
    if not IsDefined(R`JoinUnitsOverorders,set) then
        R`JoinUnitsOverorders[set]:=UnitGroup(S)+UnitGroup(T);
    end if;
    return R`JoinUnitsOverorders[set];
end intrinsic;

intrinsic InclusionOverorders(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->BoolElt
{Given an order R and two overorders S,T of R, returns whether S < T. The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`InclusionOverorders then
       R`InclusionOverorders:=AssociativeArray();
    end if;
    if not IsDefined(R`InclusionOverorders,S) then
        R`InclusionOverorders[S]:=AssociativeArray();
    end if;
    if not IsDefined(R`InclusionOverorders[S],T) then
        R`InclusionOverorders[S][T]:=S subset T;
    end if;
    return R`InclusionOverorders[S][T];
end intrinsic;

intrinsic KernelsExtensionHom(R::AlgEtQOrd, S::AlgEtQOrd)->GrpAb
{}
    if not assigned R`KernelsExtensionHoms then
        R`KernelsExtensionHoms := AssociativeArray();
    end if;
    if not IsDefined(R`KernelsExtensionHoms, S) then
        eS := ExtensionHomPicardGroups(R,S);
        R`KernelsExtensionHoms[S] := Kernel(eS);
    end if;
    return R`KernelsExtensionHoms[S];
end intrinsic;

intrinsic KernelIntersections(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->.
{Given an order R and two overorders S,T of R, returns ker(e_S) meet ker(e_T) as a subgroup of Pic(R).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`KernelIntersections then
        R`KernelIntersections := AssociativeArray();
    end if;
    key := {S,T};
    if not IsDefined(R`KernelIntersections, key) then
        R`KernelIntersections[key] := KernelsExtensionHom(R,S) meet KernelsExtensionHom(R,T);
    end if;
    return R`KernelIntersections[key];
end intrinsic;

intrinsic GSTQuotient(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->.
{Given an order R and two overorders S,T of R, returns a transversal for ker(e_S) meet ker(e_T) within Pic(R).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`GSTQuotients then
        R`GSTQuotients := AssociativeArray();
    end if;
    key := {S,T};
    if not IsDefined(R`GSTQuotients,key) then
        R`GSTQuotients[key] := Transversal(PicardGroup(R), KernelIntersections(R, S, T));
    end if;
    return R`GSTQuotients[key];
end intrinsic;

intrinsic DoubleKernelQuotient(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->.
{Given an order R and two overorders S,T of R, returns a transversal for ker(e_S) meet ker(e_T) within ker(e_T).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`DoubleKernelQuotients then
        R`DoubleKernelQuotients := AssociativeArray();
    end if;
    key := <S,T>;
    if not IsDefined(R`DoubleKernelQuotients,key) then
        eT := ExtensionHomPicardGroups(R,T);
        R`DoubleKernelQuotients[key] := Transversal(KernelsExtensionHom(R,T), KernelIntersections(R, S, T));
    end if;
    return R`DoubleKernelQuotients[key];
end intrinsic;

intrinsic TripleKernelQuotient(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd, U::AlgEtQOrd)->.
{Given an order R and three overorders S,T,U of R, returns a transversal for ker(e_T) meet (ker(e_S) + ker(e_U)) within ker(e_T).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`TripleKernelQuotients then
        R`TripleKernelQuotients := AssociativeArray();
    end if;
    key := <T,{S,U}>;
    if not IsDefined(R`TripleKernelQuotients, key) then
        kT := KernelsExtensionHom(R,T);
        R`TripleKernelQuotients[key] := Transversal(kT, KernelIntersections(R, S, T) + KernelIntersections(R, T, U));
    end if;
    return R`TripleKernelQuotients[key];
end intrinsic;

intrinsic AreIsogeniesEquivalent(x1::AlgEtQElt, I1::AlgEtQIdl, J1::AlgEtQIdl, x2::AlgEtQElt, I2::AlgEtQIdl, J2::AlgEtQIdl) -> BoolElt
{Given inclusions x1*I1<J1 and x2*I2<J2 of fractional ideals of the Frobenius order representing isogenies, return whether they are equivalent.}
    K:=Algebra(I1);
    one:=One(K);
    if I1 eq I2 then
        y:=one;
    else
        test,y:=IsIsomorphic(I1,I2); // I1=y*I2
        if not test then
            return false;
        end if;
    end if;
    if J1 eq J2 then
        z:=one;
    else
        test,z:=IsIsomorphic(J1,J2); // J1=z*J2
        if not test then
            return false;
        end if;
    end if;
    elt:=((x1*y)/(x2*z));
    inv:=1/elt;
    S:=MultiplicatorRing(I1);
    T:=MultiplicatorRing(J1);
    R:=Order(I1);
    if InclusionOverorders(R,S,T) then
        return inv in T;
    elif InclusionOverorders(R,T,S) then
        return inv in S;
    end if;
    OK:=MaximalOrder(K);
    if inv notin OK then
        return false;
    end if;
    _,uOK:=UnitGroup(OK);
    U:=JoinUnitsOverorders(R,S,T); // U = S^*T^* as a subgroup of OK^*
    return (elt@@uOK) in U;
end intrinsic;

intrinsic AreIsogeniesEquivalent(x1::AlgEtQElt, x2::AlgEtQElt, I::AlgEtQIdl, J::AlgEtQIdl)->BoolElt
{Given inclusions x1*I<J and x2*I<J of fractional ideals of the Frobenius order representing isogenies, return whether they are equivalent.}
    K:=Algebra(I);
    one:=One(K);
    elt:=x1/x2;
    inv:=1/elt;
    S:=MultiplicatorRing(I);
    T:=MultiplicatorRing(J);
    R:=Order(I);
    if InclusionOverorders(R,S,T) then
        return inv in T;
    elif InclusionOverorders(R,T,S) then
        return inv in S;
    end if;
    OK:=MaximalOrder(K);
    if elt notin OK or inv notin OK then
        return false;
    end if;
    _,uOK:=UnitGroup(OK);
    U:=JoinUnitsOverorders(R,S,T); // U = S^*T^* as a subgroup of OK^*
    return (elt@@uOK) in U;
end intrinsic;

intrinsic QuotientsUnitsOverorders(R::AlgEtQOrd,T::AlgEtQOrd,S::AlgEtQOrd)->SeqEnum
{Given an order R and two overorders T,S of R, returns a sequence of representatives in K of T^*/(S^* meet T^*). The output for each ordered pair <T,S> is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`QuotientsUnitsOverorders then
       R`QuotientsUnitsOverorders:=AssociativeArray();
    end if;
    if not IsDefined(R`QuotientsUnitsOverorders,<T,S>) then
        if InclusionOverorders(R,T,S) then
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
    if #Ms eq 0 then
        return [];
    end if;
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


//intrinsic IsogenyGraphBuilder_ModuloNothing(R::AlgEtQOrd,N::RngIntElt) -> .
intrinsic IsogenyGraphBuilder_Naive(R::AlgEtQOrd,N::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the N-isogeny graph, given as a pair classes,edges:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the N-isogeny graph.
- edges is an associative array, indexed by positive integers d. 
  edges[d] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of isogenies of degree d in the following way:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}
    icm,icm_map:=IdealClassMonoidAbstract(R);
    classes:=Classes(icm);
    edges:=AssociativeArray(:Default:=[]);
    // edges is a 1-dimensional array
    // edges[d] contains the sequence of labels of isogenies of degree d.
    for target in classes do 
        IV:=icm_map(target); //IV is a representative of each vertex, chosen once and for all
        // Ms:=[M:M in IntermediateIdeals(IV,N*IV)|ind ne 1 and N mod ind eq 0 where ind:=Index(IV,M)]; //sub-frac.R-ideals M<IV s.t. [IV:M]|N
        Ms:=SubIdealsOfIndexDividing(IV,N); //sub-frac.R-ideals M<IV s.t. [IV:M]|N
        T:=MultiplicatorRing(IV);
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            d:=Index(IV,M);
            source:=icm!M;
            IV1:=icm_map(source); //this is chosen once and for all
            test,x:=IsIsomorphic(M,IV1); //x*IV1 = M 
            assert test; // sanity check
            Append(~edges[d],<[* WEClass(source),PicClass(source) *],[* WEClass(target),PicClass(target) *],IV1,IV,x>);
        end for;
    end for;
    return [[* WEClass(target),PicClass(target) *]:target in classes],edges;
end intrinsic;

//intrinsic IsogenyGraphBuilder_ModuloPic(R::AlgEtQOrd,N::RngIntElt) -> .
intrinsic IsogenyGraphBuilder_LessNaive(R::AlgEtQOrd,N::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the N-isogeny graph, given as a pair classes,edges:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the N-isogeny graph.
- edges is an associative array, indexed by positive integers d. 
  edges[d] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of isogenies of degree d in the following way:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    classes:=[ ];
    edges:=AssociativeArray(:Default:=[]);
    // edges is a 1-dimensional array
    // edges[d] contains the sequence of labels of isogenies of degree d.
    for t in Classes(we) do 
        T:=MultiplicatorRing(t);
        eT:=ExtensionHomPicardGroups(R,T);
        PT:=PicardGroup(T);
        for bbT in PT do
            Append(~classes,[* t,bbT *]);
        end for;
        Wt:=we_map(t);
        Ms:=SubIdealsOfIndexDividing(Wt,N); //sub-frac.R-ideals M<Wt s.t. [Wt:M]|N
        assert not Wt in Ms;
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            d:=Index(Wt,M);
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
                bb:=bbT@@eT;
                //TODO Ibb, Wt*Ibb, Ws*Iaa*Ibb are computed over an over... this is not smart.
                Ibb:=pR(bb);
                Append(~edges[d],<[* s,aaS *],[* t,bbT *],Ws*Iaa*Ibb,Wt*Ibb,x>);
            end for;
        end for;
    end for;
    return classes,edges;
end intrinsic;

//intrinsic IsogenyGraphBuilder_ModuloPicUsingMinimalEdges(R::AlgEtQOrd,N::RngIntElt) -> .
intrinsic IsogenyGraphBuilder(R::AlgEtQOrd,N::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the N-isogeny graph, given as a pair classes,edges:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the N-isogeny graph.
- edges is an associative array, indexed by positive integers d. 
  edges[d] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of isogenies of degree d in the following way:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    classes:=[ ];
    edges:=AssociativeArray();
    // THIS IS WHAT I WOULD LIKE. BUT IT SEEMS BROKEN
    // edges:=AssociativeArray(:Default:=AssociativeArray(:Default:=AssociativeArray(:Default:=[])));
    // a 3 dimensional array: edges[d][T][S] where
    // - d is a positive integer (dividing N)
    // - T,S are distinguished ideals representing an ideal classes
    // is the sequence of labels of isogenies of degree d from S to T
    edges_min:=AssociativeArray(:Default:=[]);
    // a 1-dimensional array
    // edges_min[dM] is the sequence of minimal isogenies of degree dM
    for t in Classes(we) do 
        T:=MultiplicatorRing(t);
        eT:=ExtensionHomPicardGroups(R,T);
        PT:=PicardGroup(T);
        for bbT in PT do
            Append(~classes,[* t,bbT *]);
        end for;
        Wt:=we_map(t);
        Ms:=[M:M in IntermediateIdeals(Wt,N*Wt:Maximal:=true)|N mod Index(Wt,M) eq 0]; //sub-frac.R-ideals M<Wt s.t. [Wt:M]|N
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            dM:=Index(Wt,M);
            // REMOVE THE NEXT ONE?
                if not IsDefined(edges,dM) then edges[dM]:=AssociativeArray(); end if;
            source_M:=M@@icm_map;
            s:=WEClass(source_M);
            aaS:=PicClass(source_M);
            S:=MultiplicatorRing(s);
            eS:=ExtensionHomPicardGroups(R,S);
            WsIaa,Iaa,aa:=DistinguishedRepsICM(s,aaS);
            test,x:=IsIsomorphic(M,WsIaa); // x*Ws*Iaa = M
            assert test; // sanity check
            for bbT in PT do
                WtIbb,Ibb,bb:=DistinguishedRepsICM(t,bbT);
                aa1S:=eS(aa+bb);
                WsIaa1,Iaa1,aa1:=DistinguishedRepsICM(s,aa1S);
                test,y:=IsIsomorphic(S!!(Iaa*Ibb),S!!Iaa1);
                assert test;
                label:=<[* s,aa1S *],[* t,bbT *],WsIaa1,WtIbb,x*y>;
                target:=label[4];
                source:=label[3];
                Append(~edges_min[dM],label);
                // REMOVE THE NEXT TWO IF?
                    if not IsDefined(edges[dM],target) then
                        edges[dM][target]:=AssociativeArray(); // indexed by the target
                    end if;
                    if not IsDefined(edges[dM][target],source) then
                        edges[dM][target][source]:=[]; // and then the source
                    end if;
                Append(~edges[dM][target][source],label);
            end for;
        end for;
    end for;
    // now we have all minimal edges. we compose
    for n in Exclude(Divisors(N),1) do
        if not IsDefined(edges,n) then
            edges[n]:=AssociativeArray();
        end if;
        // we loop over all minimal edges E2 of degree d2
        for d2->E_min_d2 in edges_min do
            if d2 lt n and n mod d2 eq 0 then
                d1:=n div d2;
                for E2 in E_min_d2 do
                    // REMOVE?
                        if not IsDefined(edges[n],E2[4]) then edges[n][E2[4]]:=AssociativeArray(); end if;
                    // now, we loop over all already computed edges E1 of degree d1=n/d2 such
                    // that target(E1) = source(E2) = E2[3], since we want to construct the composition E2*E1
                    // (first apply the isogeny E1 then the isogeny E2)
                    //printf "n,d2,d1=%o,%o,%o,\n",n,d2,d1;
                    if IsDefined(edges,d1) and IsDefined(edges[d1],E2[3]) then
                        for E1_t->E1s in edges[d1][E2[3]] do
                            for E1 in E1s do
                                //REMOVE?
                                    if not IsDefined(edges[n][E2[4]],E1[3]) then edges[n][E2[4]][E1[3]]:=[]; end if;
                                O1:=MultiplicatorRing(E1[3]); // mult ring of source(E1)
                                O2:=MultiplicatorRing(E1[4]); // mult ring of target(E1)=source(E2)
                                O3:=MultiplicatorRing(E2[4]); // mult ring of target(E2)
                                U:=QuotientOfJoinUnitsOverOrders(R,O1,O2,O3);
                                for u in U do
                                    Ecomp:=<E1[1],E2[2],E1[3],E2[4],E1[5]*u*E2[5]>;
                                    if not exists{E:E in edges[n][E2[4]][E1[3]]|
                                        AreIsogeniesEquivalent(Ecomp[5],E[5],E[3],E[4])} then
                                        Append(~edges[n][Ecomp[4]][Ecomp[3]],Ecomp);
                                    end if;
                                end for;
                            end for;
                        end for;
                    end if;
                end for;
            end if;
        end for;
    end for;

    // this last step is just to be consistent with the other two algoritms
    edges_output:=AssociativeArray();
    for d->edges_d in edges do
        edges_output_d:=[];
        for t->edges_d_t in edges[d] do
            for s->edges_d_t_s in edges[d][t] do
                edges_output_d cat:=edges_d_t_s;
            end for;
        end for;
        if #edges_output_d gt 0 then
            edges_output[d]:=edges_output_d;
        end if;
    end for;
    return classes,edges_output;
end intrinsic;

intrinsic ConstructStandardGrphMultDir(vert::SeqEnum,edges::Assoc) -> GrphMultDir
{Given the output vert,edges produced by IsogenyGraphBuilders (or IsogenyGraphBuilder_Naive, or IsogenyGraphBuilder_LessNaive) returns the corresponding directed multi graph. The verteces of the output are labelled using integers 1,...,#vert. The i-th vertex conesponds to the ideal class vert[i].}
    n:=#vert;
    G:=MultiDigraph< n | >;
    EE:=[ ]; 
    for d->edges_d in edges do
        EE_d:=[ [Index(vert,E[1]),Index(vert,E[2])] : E in edges_d ];
        EE cat:=EE_d;
    end for;
    AddEdges(~G,EE);
    return G;
end intrinsic;

/* TESTS
   
    //AttachSpec("~/AlgEt/spec");
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");

    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    //f:=x^2 - 2*x + 5;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    Ns:=[2,4,8,16,32,2*3,2*3*5,4*9];

    // Comparing timings 3 algorithms
    for N in Ns do
        times:=[];

        K:=EtaleAlgebra(f);
        F:=PrimitiveElement(K);
        V:=q/F;
        R:=Order([F,V]);
        t0:=Cputime();
        vert,edges:=IsogenyGraphBuilder_Naive(R,N);
        Append(~times,Cputime(t0));


        //SetDebugOnError(true);
        K:=EtaleAlgebra(f);
        F:=PrimitiveElement(K);
        V:=q/F;
        R:=Order([F,V]);
        t0:=Cputime();
        vert2,edges2:=IsogenyGraphBuilder_LessNaive(R,N);
        Append(~times,Cputime(t0));
        assert #vert2 eq #vert;
        assert Keys(edges) eq Keys(edges2);
        assert forall{d:d in Keys(edges) | #edges[d] eq #edges2[d]};

        //SetDebugOnError(true);
        K:=EtaleAlgebra(f);
        F:=PrimitiveElement(K);
        V:=q/F;
        R:=Order([F,V]);
        t0:=Cputime();
        vert3,edges3:=IsogenyGraphBuilder(R,N);
        Append(~times,Cputime(t0));
        assert #vert3 eq #vert;
        assert Keys(edges) eq Keys(edges3);
        assert forall{d:d in Keys(edges) | #edges[d] eq #edges3[d]};

        printf "N=%3o, times=%o\n",N,times;
    end for;

// timings only 3rd algorithm
    //AttachSpec("~/AlgEt/spec");
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    Ns:=[2,4,8,16,32,2*3,2*3*5,4*9,2*5,3*5];
    for N in Ns do
        K:=EtaleAlgebra(f);
        F:=PrimitiveElement(K);
        V:=q/F;
        R:=Order([F,V]);
        t0:=Cputime();
        vert3,edges3:=IsogenyGraphBuilder(R,N);
        t1:=Cputime(t0);
        G3:=ConstructStandardGrphMultDir(vert3,edges3);
        is_conn:=IsConnected(UnderlyingGraph(G3));
        printf "N=%3o, t=%o, connected? %o\n",N,t1,is_conn;
    end for;
//before DistinguishedRepsICM
//N=  2, t=2.260, connected? false
//N=  4, t=3.050, connected? false
//N=  8, t=3.690, connected? false
//N= 16, t=5.180, connected? false
//N= 32, t=7.200, connected? false
//N=  6, t=4.800, connected? true
//N= 30, t=10.520, connected? true
//N= 36, t=11.790, connected? true
//N= 10, t=5.070, connected? true
//N= 15, t=4.420, connected? false
//
//after DistinguishedRepsICM
//N=  2, t=2.620, connected? false
//N=  4, t=3.160, connected? false
//N=  8, t=3.880, connected? false
//N= 16, t=5.250, connected? false
//N= 32, t=7.270, connected? false
//N=  6, t=4.280, connected? true
//N= 30, t=9.340, connected? true
//N= 36, t=11.450, connected? true
//N= 10, t=5.400, connected? true
//N= 15, t=4.880, connected? false

    
    // 3rd Algorithm, with Profiler.
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    SetProfile(true);
    vert3,edges3:=IsogenyGraphBuilder(R,36);
    SetProfile(false);
    G:=ProfileGraph();




*/


