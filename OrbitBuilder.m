

intrinsic GSTAct(g::GrpAbElt, phi::Tup)->Tup
{Given an element g of Pic(R) and an isogeny phi from I to J represented by a tuple, returns g*phi as a tuple, mapping from the canonical rep of [g*I] to the canonical rep of [g*J].  Note that this only an action up to equivalence: g*h*phi may not be equal to g*(h*phi), but is guaranteed to be equivalent to it}
    s, hS := Explode(phi[1]);
    t, hT := Explode(phi[2]);
    I := phi[3];
    J := phi[4];
    x := phi[5];
    R := Order(I);
    PR,pR:=PicardGroup(R);
    //we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    //Ws:=we_map(s);
    //Wt:=we_map(t);
    S := MultiplicatorRing(s);
    T := MultiplicatorRing(t);
    eS := ExtensionHomPicardGroups(R,S);
    eT := ExtensionHomPicardGroups(R,T);

    gS := (g@eS)+hS;
    gT := (g@eT)+hT;

    // FIXME: DistinguishedICMRep from Misc.m should help here
    G := g@pR;
    gI := DistinguishedRepsICM(s, gS);
    gJ := DistinguishedRepsICM(t, gT);
    //gI := Ws*((gS@@eS)@pR);
    //gJ := Wt*((gT@@eT)@pR);

    test,y := IsIsomorphic(G*I, gI);
    assert test;
    test,z := IsIsomorphic(gJ, G*J);
    assert test;

    return <[* s,gS *], [* t,gT *], gI, gJ, y*x*z>;
end intrinsic;

intrinsic GSTOrbit(phi::Tup)->SeqEnum
{Given an isogeny phi from I to J represented by a tuple, returns the orbit G_(S,T)*phi}
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
    eS := ExtensionHomPicardGroups(R,S);
    eT := ExtensionHomPicardGroups(R,T);

    orb := [];
    for g in DoubleKernelQuotient(R, S, T) do
        gS := (g@eS)+hS;
        gT := (g@eT)+hT;
        G := g@pR;
        // FIXME: DistinguishedICMRep from Misc.m should help here
        gI := Ws*((gS@@eS)@pR);
        gJ := Wt*((gT@@eT)@pR);

        test,y := IsIsomorphic(G*I, gI);
        assert test;
        test,z := IsIsomorphic(gJ, G*J);
        assert test;

        Append(~orb, <[* s,gS *], [* t,gT *], gI, gJ, y*x*z>);
    end for;
    return orb;
end intrinsic;

intrinsic AreIsogeniesGSTEquivalent(x1::AlgEtQElt,I1::AlgEtQIdl,J1::AlgEtQIdl,x2::AlgEtQElt,I2::AlgEtQIdl,J2::AlgEtQIdl)->BoolElt
{//TODO
}
    // FIXME: You are starting from the label (inclusion of ideals) and then you look up for the vertices.
    // This is time consuming. Can be avoided? For example including the whole Tup ?
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
    x2 := psi[5];

    R := Order(psi[3]);
    if Order(psi[4]) ne R then
        error "isogenies must be in the same isogeny class";
    end if;
    T := MultiplicatorRing(t2);
    eT := ExtensionHomPicardGroups(R, T);
    U := MultiplicatorRing(u2);

    s1, hS1 := Explode(phi[1]);
    t1, hT1 := Explode(phi[2]);
    if t1 ne t2 then
        error "Domain of second isogeny not weakly equivalent to codomain of first isogeny";
    end if;

    // Act so that the domain of psi matches the codomain of phi
    phi1 := GSTAct((hT2 - hT1)@@eT, phi);
    assert phi1[4] eq psi[3];

    if Order(phi1[3]) ne R then
        error "isogenies must be in the same isogeny class";
    end if;

    S := MultiplicatorRing(s1);

    ans := [];
    for g1 in TripleKernelQuotient(R, S, T, U) do
        g1phi := GSTAct(g1, phi1);
        assert g1phi[4] eq psi[3];
        x1 := g1phi[5];
        for z in QuotientOfJoinUnitsOverOrders(R, S, T, U) do
            zz := x1 * z * x2;
            I := g1phi[3];
            J := psi[4];
            assert zz * I subset J;
            Append(~ans, <g1phi[1], psi[2], g1phi[3], psi[4], x1 * z * x2>);
        end for;
    end for;
    return ans;
end intrinsic;

function compute_orbits_GSUT_on_Ms(T, Ms, R, Wt)
    // Analogue of compute_orbits_UT_on_Ms from IsogenyGraphBuilders.m
    // But also taking representatives for the orbit of G_{S,T} (in order to stay among the ideals in Ms, only have an action of ker(eT) / (ker(eT) meet ker(eS)))
    if #Ms eq 0 then
        return 0;
    end if;
    remaining := {@ M:M in Ms @};
    orbits := [];
    icm, icm_map := IdealClassMonoidAbstract(R);
    PR, pR := PicardGroup(R);
    repeat
        M1 := remaining[1];
        Append(~orbits, M1);
        // We compute the orbit of M1:
        // If S is the multiplicator ring of M1, then S^* acts trivially on M1.
        // So, the orbit of M1 by the action of T^* can be computed using the finite quotient T^*/(S^* meet T^*)
        // Reps in K of this quotient are stored in the associative array R`QuotientsUnitsOverorders[<T,S>], 
        // which is populated on demand by the corresponding intrinsc, to avoid useless recomputation.
        S := MultiplicatorRing(M1);
        UST := QuotientsUnitsOverorders(R, T, S);
        for g in DoubleKernelQuotient(R, S, T) do
            I := g @ pR;
            test,y := IsIsomorphic(Wt, I * Wt); // TODO: Check that reversing this was right
            assert test;
            gM1 := y * I * M1;
            assert gM1 subset Wt;
            orbit_gM1 := {@ v * gM1 : v in UST @};
            remaining diff:= orbit_gM1;
        end for;
    until #remaining eq 0;
    return orbits;
end function;

intrinsic IsogenyOrbitBuilder(R::AlgEtQOrd,D::RngIntElt : dual_only:=false) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer D, returns an associative array whose value at each integer d dividing D is a sequence of isogenies of degree d so that the set of all isogenies of degree d is obtained by taking orbits for the action of G_(s,t) on each representative.  If the optional parameter dual_only is set, only isogenies mapping from a weak equivalence class to its dual will be included in the output.}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);
    dual_we:= AssociativeArray();

    reps:=AssociativeArray();
    reps_min:=AssociativeArray(:Default:=[]);
    // a 1-dimensional array
    // reps_min[dM] is the sequence of minimal isogenies of degree dM
    for t in Classes(we) do
        T := MultiplicatorRing(t);
        eT := ExtensionHomPicardGroups(R, T);
        Wt := we_map(t);
        dual_we[t] := TraceDualIdeal(ComplexConjugate(Wt)) @@ we_map;
        Ms := [M : M in IntermediateIdeals(Wt, D*Wt : Maximal:=true) | D mod Index(Wt, M) eq 0]; //sub-frac.R-ideals M<Wt s.t. [Wt:M]|D
        Ms:=compute_orbits_GSUT_on_Ms(T, Ms, R, Wt);
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
            label := <[* s,aaS *],[* t, PR.0@eT *], WsIaa, Wt, x>;
            for olabel in reps_min[dM] do
                assert not AreIsogeniesEquivalent(label[5], label[3], label[4], olabel[5], olabel[3], olabel[4]);
            end for;
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

    // FIXME - remove this block once done debugging
    /*for d->reps_d in reps do
        for t->reps_d_t in reps[d] do
            for s->reps_d_t_s in reps[d][t] do
                if #reps_d_t_s eq 2 then //FIXME Stefano: why testing only for eq 2 and not ge 2?
                    phi, psi := Explode(reps_d_t_s);
                    assert not AreIsogeniesEquivalent(phi[5],phi[3],phi[4],psi[5],psi[3],psi[4]);
                end if;
            end for;
        end for;
    end for;*/
    // FIXME - remove this block once done debugging

    // now we have all minimal reps. we compose
    for n in Exclude(Divisors(D), 1) do
        if not IsDefined(reps, n) then
            reps[n]:=AssociativeArray();
        end if;
        // we loop over all minimal reps E2 of degree d2
        for d2->E_min_d2 in reps_min do
            if d2 lt n and n mod d2 eq 0 then
                d1 := n div d2;
                for E2 in E_min_d2 do
                    E2_s := E2[1][1];
                    // REMOVE?
                        if not IsDefined(reps[d1], E2_s) then reps[d1][E2_s] := AssociativeArray(); end if;
                    // now, we loop over all already computed reps E1 of degree d1=n/d2 such
                    // that target(E1) = source(E2) = E2[1][1], since we want to construct the composition E1*E2
                    // (first apply the isogeny E1 then the isogeny E2)
                    for E1_t->E1s in reps[d1][E2_s] do
                        if n eq D and dual_only and E1_t ne dual_we[E2_s] then
                            // We don't need degree D isogenies for further composition, so skip if not needed for output.
                            continue;
                        end if;
                        for E1 in E1s do
                            //REMOVE?
                                if not IsDefined(reps[n], E2[2][1]) then reps[n][E2[2][1]] := AssociativeArray(); end if;
                                if not IsDefined(reps[n][E2[2][1]],E1[1][1]) then reps[n][E2[2][1]][E1[1][1]]:=[]; end if;
                            for Ecomp in GSTCompose(E1, E2) do
                                //if not exists{E:E in reps[n][E2[2][1]][E1[1][1]]|
                                if not IsDefined(reps[n], Ecomp[2][1]) then reps[n][Ecomp[2][1]] := AssociativeArray(); end if;
                                if not IsDefined(reps[n][Ecomp[2][1]], Ecomp[1][1]) then reps[n][Ecomp[2][1]][Ecomp[1][1]] := []; end if;
                                if not exists{E:E in reps[n][Ecomp[2][1]][Ecomp[1][1]]|
                                    AreIsogeniesGSTEquivalent(Ecomp[5],Ecomp[3],Ecomp[4],E[5],E[3],E[4])} then
                                    // Asserts for debugging
                                    //assert not exists{E:E in reps[n][Ecomp[2][1]][Ecomp[1][1]]|AreIsogeniesEquivalent(Ecomp[5],Ecomp[3],Ecomp[4],E[5],E[3],E[4])};
                                    //if #reps[n][Ecomp[2][1]][Ecomp[1][1]] eq 1 then
                                    //    EE := reps[n][Ecomp[2][1]][Ecomp[1][1]][1];
                                    //    assert not AreIsogeniesEquivalent(Ecomp[5],Ecomp[3],Ecomp[4],EE[5],EE[3],EE[4]);
                                    //end if;
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
                if dual_only and t ne dual_we[s] then
                    continue;
                end if;
                // For debugging
                //if #reps_d_t_s eq 2 then
                //    phi, psi := Explode(reps_d_t_s);
                //    assert not AreIsogeniesEquivalent(phi[5],phi[3],phi[4],psi[5],psi[3],psi[4]);
                //end if;
                reps_output_d cat:=reps_d_t_s;
            end for;
        end for;
        reps_output[d]:=reps_output_d;
    end for;
    return reps_output;
end intrinsic;

intrinsic DualIsogenies_FromOrbit(R::AlgEtQOrd,D::RngIntElt)->Assoc
{Given the Frobenius order R of an isogeny class of ordinary squarefree abelian varieties over a finite field and an integer D>1, it returns an associative array isog, indexed by divisors d>1 of D where isog[d] is a sequence of isogenies from A to the dual of A, representing all equivalence classes of such isogenies.}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);
    reps := IsogenyOrbitBuilder(R, D : dual_only:=true);
    duals := AssociativeArray();
    Js := AssociativeArray();
    homs := AssociativeArray();
    for s in Classes(we) do
        Ws := we_map(s);
        t := ComplexConjugate(we_map(s))@@we_map;
        duals[s] := t;
        Wt := we_map(t);
        Wtdual := TraceDualIdeal(ComplexConjugate(Wt));
        Js[s] := PicClass(ColonIdeal(Wtdual, Ws) @@ icm_map);

        S := MultiplicatorRing(s);
        if not IsDefined(homs, S) then
            Sbar := ComplexConjugate(S);
            GSS, proj := GSTQuotient(R, S, Sbar);
            beta := hom<GSS -> GSS | [<GSS.i, GSS.i + (ComplexConjugate(((GSS.i) @@ proj) @ pR) @@ pR) @ proj> : i in [1..Ngens(GSS)]]>;

            eS := ExtensionHomPicardGroups(R,S);
            PicS := Codomain(eS);
            eSb := ExtensionHomPicardGroups(R,Sbar);
            PicSbar := Codomain(eSb);
            bar := hom<PicS -> PicSbar | [<PicS.i, ComplexConjugate((PicS.i @@ eS) @ pR) @@ pR @ eS> : i in [1..Ngens(PicS)]]>;
            X, i1, i2 := DirectSum(PicS, PicSbar);
            prod_proj := hom<GSS -> X | [<GSS.i, ((GSS.i @@ proj) @ eS) @ i1 + ((GSS.i @@ proj) @ eSb) @ i2> : i in [1..Ngens(GSS)]]>;
            homs[S] := <beta, proj, prod_proj, i1, i2, bar>;
        end if;
    end for;
    ans := AssociativeArray();
    for d->rep_d in reps do
        ans[d] := [];
        for phi in rep_d do
            s := phi[1][1];
            t := phi[2][1];
            if t ne duals[s] then
                continue;
            end if;
            S := MultiplicatorRing(s);
            Sbar := ComplexConjugate(S);
            beta, proj, prod_proj, i1, i2, bar := Explode(homs[S]);
            aa := phi[1][2];
            ap1 := Js[s] - aa;
            ap2 := ap1 @ bar;
            try
                b0 := ((ap1 @ i1) + (ap2 @ i2)) @@ prod_proj @@ beta;
            catch err
                continue;
            end try;
            for c in Kernel(beta) do
                // TODO: Need to adjust by iota
                Append(~ans[d], GSTAct((b0 + c) @@ proj, phi));
            end for;
        end for;
    end for;
    return ans;
end intrinsic;

intrinsic IsogenyGraphBuilder_FromOrbit(R::AlgEtQOrd,D::RngIntElt,A::Assoc) -> .
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

intrinsic IsogenyGraphChecker(R::AlgEtQOrd, D::RngIntElt : reps:=0, classes:=0, edges:=0) -> SeqEnum, Assoc, Assoc
{Checks that the number of isogenies between each pair of weak equivalence classes predicted by IsogenyGraphBuilder and IsogenyOrbitBuilder agrees}
    if reps cmpeq 0 then
        reps := IsogenyOrbitBuilder(R, D);
    end if;
    by_orb := AssociativeArray(:Default:=0);
    for d->reps_d in reps do
        print "Orbit", d, #reps_d;
        for phi in reps_d do
            s := phi[1][1];
            t := phi[2][1];
            S := MultiplicatorRing(s);
            T := MultiplicatorRing(t);
            by_orb[<d,s,t>] +:= #GSTTransversal(R, S, T);
        end for;
    end for;

    if classes cmpeq 0 then
        classes, edges := IsogenyGraphBuilder(R, D);
    end if;
    by_edge := AssociativeArray(:Default:=0);
    for d->edges_d in edges do
        print "NoOrbit", d, #edges_d;
        for phi in edges_d do
            s := phi[1][1];
            t := phi[2][1];
            by_edge[<d,s,t>] +:= 1;
        end for;
    end for;

    mismatches := [<key, by_orb[key], by_edge[key]> : key in Keys(by_orb) join Keys(by_edge) | by_orb[key] ne by_edge[key]];

    return mismatches, reps, edges, by_orb, by_edge;
end intrinsic;
