

intrinsic GSTAct(g::GrpAbElt, phi::Tup)->Tup
{Given an element g of Pic(R) and an isogeny phi from I to J represented by a tuple, returns g*phi as a tuple, mapping from the canonical rep of [g*I] to the canonical rep of [g*J].  Note that this only an action up to equivalence: g*h*phi may not be equal to g*(h*phi), but is guaranteed to be equivalent to it}
    s, hS := Explode(phi[1]);
    t, hT := Explode(phi[2]);
    I := phi[3];
    J := phi[4];
    x := phi[5];
    R := Order(I);
    PR,pR:=PicardGroup(R);
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    Ws:=we_map(s);
    Wt:=we_map(t);
    S := MultiplicatorRing(s);
    T := MultiplicatorRing(t);
    eS := ExtensionHomPicardGroup(R,S);
    eT := ExtensionHomPicardGroup(R,T);

    gS := (g@eS)+hS;
    gT := (g@eT)+hT;

    G := g@pR;
    gI := Ws*((gS@@eS)@pR); // TODO: need this to be canonical, but there can be multiple pullbacks along eS.  Maybe should just map using pS?
    gJ := Wt*((gT@@eT)@pR);

    test,y := IsIsomorphic(gI, G*I);
    assert test;
    test,z := IsIsomorphic(G*J, gJ);
    assert test;

    return <[* s,gS *], [* t,gT *], gI, gJ, y*x*z>;
end intrinsic;

intrinsic GSTOrbit(phi::Tup)->SeqEnum
{Given an isogeny phi from I to J represented by a tuple, returns the orbit G_{S,T}*phi}
    s, hS := Explode(phi[1]);
    t, hT := Explode(phi[2]);
    I := phi[3];
    J := phi[4];
    x := phi[5];
    R := Order(I);
    PR,pR := PicardGroup(R);
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    Ws := we_map(s);
    Wt := we_map(t);
    S := MultiplicatorRing(s);
    T := MultiplicatorRing(t);
    eS := ExtensionHomPicardGroup(R,S);
    eT := ExtensionHomPicardGroup(R,T);

    // TODO: Should cache these kernels and their intersections
    K := Kernel(eS) meet Kernel(eT);
    orb := [];
    for g in RightTransversal(PR, K) do
        // TODO: It would be nice to reuse some of the work here...
        gS := (g@eS)+hS;
        gT := (g@eT)+hT;
        G := g@pR;
        gI := Ws*((gS@@eS)@pR);
        gJ := Wt*((gT@@eT)@pR);

        test,y := IsIsomorphic(gI, G*I);
        assert test;
        test,z := IsIsomorphic(G*J, gJ);
        assert test;

        Append(~orb, <[* s,gS *], [* t,gT *], gI, gJ, y*x*z>);
    end for;
    return orb;
end intrinsic;

intrinsic AreIsogeniesGSTEquivalent(x1::AlgEtQElt,I1::AlgEtQIdl,J1::AlgEtQIdl,x2::AlgEtQElt,I2::AlgEtQIdl,J2::AlgEtQIdl)->BoolElt
{}
    R := Order(I1);
    PR,pR := PicardGroup(R);
    assert R eq Order(I2) and R eq Order(J1) and R eq Order(J2);
    icm,icm_map := IdealClassMonoidAbstract(R);
    source1 := I1@@icm_map;
    source2 := I2@@icm_map;
    s := WEClass(source1);
    if s ne WEClass(source2) then
        return false;
    end if;
    S := MultiplicatorRing(source1);
    target1 := J1@@icm_map;
    target2 := J2@@icm_map;
    t := WEClass(target1);
    if t ne WEClass(target2) then
        return false;
    end if;
    T := MultiplicatorRing(target1);

    eS := ExtensionHomPicardGroups(R,S);
    KS := Kernel(eS);
    eT := ExtensionHomPicardGroups(R,T);
    KT := Kernel(eT);
    gS := (PicClass(source2) - PicClass(source1))@@eS;
    gT := (PicClass(target2) - PicClass(target1))@@eT;
    g := gS - gT;
    // Want to express gS - gT = ks + kt, since then (gS - ks) = (gT + kt) is an element with the right image under eS and under eT
    KSKT, incs, projs := DirectSum([KS,KT]);
    pS, pT := Explode(projs);
    Ksum := hom<KSKT->PR | [<KSKT.i,pS(KSKT.i)+pT(KSKT.i)> : i in [1..Ngens(KSKT)]]>;
    try
        ks := (g @@ Ksum) @ pS;
    catch e
        return false;
    end try;
    iso1 := GSTAct(gS - ks, <[* s, PicClass(source1) *], [* t, PicClass(target1) *], I1, J1, x1>);
    return AreIsogeniesEquivalent(iso1[5], iso1[3], iso1[4], x2, I2, J2);
end intrinsic;

intrinsic GSTCompose(phi::Tup, psi::Tup)->SeqEnum
{Given two isogenies where the weak equivalence class of the domain of psi is the same as the weak equivalence class of the codomain of phi, and that map between canonical representatives, return all possible compositions (up to equivalence)}
    t2, hT2 := Explode(psi[1]);
    u2, hU2 := Explode(psi[2]);
    J2 := psi[3];
    K2 := psi[4];
    x2 := psi[5];

    R := Order(J2);
    if Order(K2) ne R then
        error "isogenies must be in the same isogeny class";
    end if;
    T := MultiplicatorRing(t2);
    eT := ExtensionHomPicardGroups(R,T);
    U := MultiplicatorRing(u2);
    eU := ExtensionHomPicardGroups(R,U);

    t1, hT1 := Explode(phi[2]);
    if t1 ne t2 then
        error "Domain of second isogeny not weakly equivalent to codomain of first isogeny";
    end if;

    // Act so that the domain of psi matches the codomain of phi
    phi := GSTAct((hT2 - hT2)@@eT, phi);

    s1, hS1 := Explode(phi[1]);
    I1 := phi[3];
    J1 := phi[4];
    x1 := phi[5];
    assert J1 eq J2;

    if Order(I1) ne R then
        error "isogenies must be in the same isogeny class";
    end if;

    S := MultiplicatorRing(s1);
    eS := ExtensionHomPicardGroups(R,S);

    kS := Kernel(eS);
    kT := Kernel(eT);
    kU := Kernel(eU);
    kST := kS meet kT;
    //for g1 in Transversal(kT, kST) do
    
    // Since we can act to change the codomain to anything in u2, we leave it the same ([* u2, hU2 *] = K2)
    // We then need to iterate over g2 in ker(eU) / (ker(eU) meet ker(eT))
    // and g1 in ker(eT) / (ker(eT) meet ker(eS)), acting on psi by g2 and on phi by g1+g2.
    // We can quotient the result by ker(eU) / (ker(eU) meet ker(eS)),
    // since this gives the action of G_{S,U} fixing the overall codomain.
    // The result is that we need to loop over pairs g1, g2 so that g1+g2 in ker(eS) and check which compositions are equivalent to each other
    // We can also apply another kind of transformation: composing with an element of OT^x / (OS^x * OU^x).  
    // TODO: Finish

end intrinsic;

function compute_orbits_GSUT_on_Ms(T,Ms,R)
    // Analogue of compute_orbits_UT_on_Ms from IsogenyGraphBuilders.m
    // But also taking representatives for the orbit of G_{S,T} (in order to stay among the ideals in Ms, only have an action of ker(eT) / (ker(eT) meet ker(eS)))

    // TODO: Finish
end function;

intrinsic IsogenyOrbitBuilder(R::AlgEtQOrd,N::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns an associative array whose value at each integer d dividing N is a sequence of isogenies of degree d so that the set of all isogenies of degree d is obtained by taking orbits for the action of G_{s,t} on each representative}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    reps:=AssociativeArray();
    reps_min:=AssociativeArray(:Default:=[]);
    // a 1-dimensional array
    // reps_min[dM] is the sequence of minimal isogenies of degree dM
    for t in Classes(we) do
        T := MultiplicatorRing(t);
        Wt := we_map(t);
        Ms := [M : M in IntermediateIdeals(Wt, N*Wt : Maximal:=true) | N mod Index(Wt, M) eq 0]; //sub-frac.R-ideals M<Wt s.t. [Wt:M]|N
        Ms:=compute_orbits_GSUT_on_Ms(T,Ms,R);
        for M in Ms do
            dM := Index(Wt,M);
            // REMOVE THE NEXT ONE?
                if not IsDefined(reps,dM) then reps[dM]:=AssociativeArray(); end if;
            source_M := M@@icm_map;
            s := WEClass(source_M);
            aaS := PicClass(source_M);
            WsIaa, Iaa, aa := DistinguishedRepsICM(s, aaS);
            test, x := IsIsomorphic(M, WsIaa); // x*Ws*Iaa = M
            assert test; // sanity check
            label := <[* s,aaS *],[* t,Identity(T) *], WsIaa, Wt, x>;
            Append(~reps_min[dM], label);
            // REMOVE THE NEXT TWO IF?
                if not IsDefined(reps[dM],t) then
                    reps[dM][t]:=AssociativeArray(); // indexed by the target
                end if;
                if not IsDefined(reps[dM][t], s) then
                    reps[dM][t][s]:=[]; // and then the source
                end if;
            Append(~reps[dM][t][s], label);
        end for;
    end for;
    // now we have all minimal reps. we compose
    for n in Exclude(Divisors(N), 1) do
        if not IsDefined(reps, n) then
            reps[n]:=AssociativeArray();
        end if;
        // we loop over all minimal reps E2 of degree d2
        for d2->E_min_d2 in reps_min do
            if d2 lt n and n mod d2 eq 0 then
                d1 := n div d2;
                for E2 in E_min_d2 do
                    // REMOVE?
                        if not IsDefined(reps[n], E2[2][1]) then reps[n][E2[2][1]] := AssociativeArray(); end if;
                    // now, we loop over all already computed reps E1 of degree d1=n/d2 such
                    // that target(E1) = source(E2) = E2[1][1], since we want to construct the composition E1*E2
                    // (first apply the isogeny E1 then the isogeny E2)
                    for E1_t->E1s in reps[d1][E2[1][1]] do
                        for E1 in E1s do
                            //REMOVE?
                                if not IsDefined(reps[n][E2[2][1]],E1[1][1]) then reps[n][E2[2][1]][E1[1][1]]:=[]; end if;
                            for Ecomp in GSTCompose(E1, E2) do
                                if not exists{E:E in reps[n][E2[2][1]][E1[1][1]]|
                                    AreIsogeniesGSTEquivalent(Ecomp[5],Ecomp[3],Ecomp[4],E[5],E[3],E[4])} then
                                    Append(~reps[n][Ecomp[2][1]][Ecomp[1][1]], Ecomp);
                                end if;
                            end for;
                        end for;
                    end for;
                end for;
            end if;
        end for;
    end for;

    // this last step is just to be consistent with the other two algoritms
    reps_output:=AssociativeArray();
    for d->reps_d in reps do
        reps_output_d:=[];
        for t->reps_d_t in reps[d] do
            for s->reps_d_t_s in reps[d][t] do
                reps_output_d cat:=reps_d_t_s;
            end for;
        end for;
        reps_output[d]:=reps_output_d;
    end for;
    return reps_output;
end intrinsic;

intrinsic IsogenyGraphBuilder_FromOrbit(R::AlgEtQOrd,N::RngIntElt,A::Assoc) -> .
{Converts the output of IsogenyOrbitBuilder into the same format as the output of IsogenyGraphBuilder for comparison}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    classes:=[ ];
    edges_output:=AssociativeArray();
    for d in Keys(A) do
        edges_output[d] := [];
    end for;
    for t in Classes(we) do
        T:=MultiplicatorRing(t);
        PT:=PicardGroup(T);
        for bbT in PT do
            Append(~classes,[* t,bbT *]);
        end for;
        for d->edges_d in A do
            if IsDefined(A[d], t) then
                for s->edges_d_t_s in A[d][t] do
                    for rep in edges_d_t_s do
                        edges_output[d] cat:= GSTOrbit(rep);
                    end for;
                end for;
            end if;
        end for;
    end for;
    return classes, edges_output;
end intrinsic;

intrinsic IsogenyGraphChecker(R::AlgEtQOrd, N::RngIntElt)
{Checks that the number of isogenies between each pair of weak equivalence classes predicted by IsogenyGraphBuilder and IsogenyOrbitBuilder agrees}
    PR,pR:=PicardGroup(R);
    reps := IsogenyOrbitBuilder(R, N);
    by_orb := AssociativeArray(:Default:=0);
    for d->reps_d in reps do
        for phi in reps_d do
            s := phi[1][1];
            t := phi[2][1];
            S := MultiplicatorRing(s);
            T := MultiplicatorRing(t);
            eS := ExtensionHomPicardGroups(R, S);
            eT := ExtensionHomPicardGroups(R, T);
            KS := Kernel(eS);
            KT := Kernel(eT);
            K := KS meet KT;
            // TODO: as noted above, we should cache these kernels, maps, intersection, etc
            by_orb[<d,s,t>] +:= #PR / #K;
        end for;
    end for;

    classes, edges := IsogenyGraphBuilder(R, N);
    by_edge := AssociativeArray(:Default:=0);
    for d->edges_d in edges do
        for phi in edges_d do
            s := phi[1][1];
            t := phi[2][1];
            by_edge[<d,s,t>] +:= 1;
        end for;
    end for;

    mismatches := [<key, by_orb[key], by_edge[key]> : key in Keys(by_orb) join Keys(by_edge) | by_orb[key] ne by_edge[key]];

    return mismatches, reps, edges;
end intrinsic;
