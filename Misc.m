/*
    This file contains a series of intrinsics devoted to populate 
    attributes of the Frobenius order of an isogeny class. 
    Their purpose is to increase the speed of the isogeny algorithms
    by avoiding unncecessary recomputations.
*/


declare attributes AlgEtQOrd: QuotientsUnitsOverorders, // transversals in K of T^*/(S^* meet T^*)
                              QuotientOfJoinUnitsOverOrders, // transversals in K of O2^*/(O1^*O3^* meet O2^*)
                              InclusionOverorders, // whether S < T
                              JoinUnitsOverorders, // S^*T^* as a subgroup of OK^*
                              KernelsExtensionHoms, // ker(e_S)
                              KernelIntersections, // ker(e_S) meet ker(e_T) as a subgroup of Pic(R)
                              GSTTransversals, // Pic(R) / ker(e_S) meet ker(e_T)
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

intrinsic SubIdealsOfIndexDividing(I::AlgEtQIdl,D:RngIntElt)->SetIndx[AlgEtQIdl]
{Given a fractional R-ideal I and a positive integer D, returns all fractional R-ideals J < I such that [I:J] divides D. They are produced recursively from the maximal ones. I is not part of the output.}
    if D eq 1 then
        return {@ I @};
    end if;
    J:=D*I;
    queue:={@ I @};
    output:={@ @};
    done:={@ @};
    while #queue gt 0 do
        pot_new:=&join[_MaximalIntermediateIdeals(elt,J) : elt in queue ];
        pot_new:={@ K : K in pot_new | D mod Index(I,K) eq 0 @}; // we keep only the ones whose index divides D 
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
    o13:={myHash(O1),myHash(O3)};
    key:=<myHash(O2),o13>;
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
    set:={myHash(S),myHash(T)};
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
    S_hash:=myHash(S);
    T_hash:=myHash(T);
    if not IsDefined(R`InclusionOverorders,S_hash) then
        R`InclusionOverorders[S_hash]:=AssociativeArray();
    end if;
    if not IsDefined(R`InclusionOverorders[S_hash],T_hash) then
        R`InclusionOverorders[S_hash][T_hash]:=S subset T;
    end if;
    return R`InclusionOverorders[S_hash][T_hash];
end intrinsic;

intrinsic KernelsExtensionHom(R::AlgEtQOrd, S::AlgEtQOrd)->GrpAb
{Return the kernel of the group homorphism Pic(R)->Pic(S) induced by the extension map I->IS. The output is stored in an AssociativeArray in an attribute of R, which is populated on demand.}
    if not assigned R`KernelsExtensionHoms then
        R`KernelsExtensionHoms := AssociativeArray();
    end if;
    if not IsDefined(R`KernelsExtensionHoms, myHash(S)) then
        eS := ExtensionHomPicardGroups(R,S);
        R`KernelsExtensionHoms[myHash(S)] := Kernel(eS);
    end if;
    return R`KernelsExtensionHoms[myHash(S)];
end intrinsic;

intrinsic KernelIntersections(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->.
{Given an order R and two overorders S,T of R, returns ker(e_S) meet ker(e_T) as a subgroup of Pic(R).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`KernelIntersections then
        R`KernelIntersections := AssociativeArray();
    end if;
    key := {myHash(S),myHash(T)};
    if not IsDefined(R`KernelIntersections, key) then
        R`KernelIntersections[key] := KernelsExtensionHom(R,S) meet KernelsExtensionHom(R,T);
    end if;
    return R`KernelIntersections[key];
end intrinsic;

intrinsic GSTTransversal(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->.
{Given an order R and two overorders S,T of R, returns a transversal for ker(e_S) meet ker(e_T) within Pic(R).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`GSTTransversals then
        R`GSTTransversals := AssociativeArray();
    end if;
    key := {myHash(S),myHash(T)};
    if not IsDefined(R`GSTTransversals,key) then
        R`GSTTransversals[key] := Transversal(PicardGroup(R), KernelIntersections(R, S, T));
    end if;
    return R`GSTTransversals[key];
end intrinsic;

intrinsic GSTQuotient(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->GrpAb, Map
{Given an order R and two overorders S,T of R, returns the quotient Pic(R) / (ker(e_S) meet ker(e_T)).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`GSTQuotients then
        R`GSTQuotients := AssociativeArray();
    end if;
    key := {myHash(S),myHash(T)};
    if not IsDefined(R`GSTQuotients,key) then
        GST, proj := quo<PicardGroup(R) | KernelIntersections(R, S, T)>;
        R`GSTQuotients[key] := <GST, proj>;
    end if;
    return Explode(R`GSTQuotients[key]);
end intrinsic;

intrinsic DoubleKernelQuotient(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd)->.
{Given an order R and two overorders S,T of R, returns a transversal for ker(e_S) meet ker(e_T) within ker(e_T).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`DoubleKernelQuotients then
        R`DoubleKernelQuotients := AssociativeArray();
    end if;
    key := <myHash(S),myHash(T)>;
    if not IsDefined(R`DoubleKernelQuotients,key) then
        eT := ExtensionHomPicardGroups(R,T);
        K := KernelsExtensionHom(R,T);
        if #K eq 1 then // Magma bug?
           R`DoubleKernelQuotients[key] := [K.0];
        else
            R`DoubleKernelQuotients[key] := Transversal(K, KernelIntersections(R, S, T));
        end if;
    end if;
    return R`DoubleKernelQuotients[key];
end intrinsic;

intrinsic TripleKernelQuotient(R::AlgEtQOrd, S::AlgEtQOrd, T::AlgEtQOrd, U::AlgEtQOrd)->.
{Given an order R and three overorders S,T,U of R, returns a transversal for ker(e_T) meet (ker(e_S) + ker(e_U)) within ker(e_T).  The output is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`TripleKernelQuotients then
        R`TripleKernelQuotients := AssociativeArray();
    end if;
    key := <myHash(T),{myHash(S),myHash(U)}>;
    if not IsDefined(R`TripleKernelQuotients, key) then
        kT := KernelsExtensionHom(R,T);
//        R`TripleKernelQuotients[key] := Transversal(kT, KernelIntersections(R, S, T) + KernelIntersections(R, T, U));
        R`TripleKernelQuotients[key] := Transversal(kT, sub<kT|Generators(KernelIntersections(R, S, T) + KernelIntersections(R, T, U))>);
    end if;
    return R`TripleKernelQuotients[key];
end intrinsic;

intrinsic QuotientsUnitsOverorders(R::AlgEtQOrd,T::AlgEtQOrd,S::AlgEtQOrd)->SeqEnum
{Given an order R and two overorders T,S of R, returns a sequence of representatives in K of T^*/(S^* meet T^*). The output for each ordered pair <T,S> is stored in an associative array attribute of R, which is populated on demand.}
    if not assigned R`QuotientsUnitsOverorders then
       R`QuotientsUnitsOverorders:=AssociativeArray();
    end if;
    key:=<myHash(T),myHash(S)>;
    if not IsDefined(R`QuotientsUnitsOverorders,key) then
        if InclusionOverorders(R,T,S) then
            // if T < S then T^* < S^*, so the quotient is trivial
            R`QuotientsUnitsOverorders[key]:=[One(Algebra(R))];
        else
            UT,UTmap:=UnitGroup(T);
            US,USmap:=UnitGroup(S);
            if UT subset US then
                // this choice of transversal might make things faster later
                R`QuotientsUnitsOverorders[key]:=[One(Algebra(R))];
            else
                R`QuotientsUnitsOverorders[key]:=[UTmap(v):v in Transversal(UT,UT meet US)];
            end if;
        end if;
    end if;
    return R`QuotientsUnitsOverorders[key];
end intrinsic;
