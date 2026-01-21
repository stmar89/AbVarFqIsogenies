// testing various versions of the algorithm
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    all:=Split(Read("weil_poly_sqfree_ord.txt"));
    PP<x>:=PolynomialRing(Integers());
    for c in all do
        h:=PP!eval(c);
        if Degree(h) eq 4 then
            K:=EtaleAlgebra(h);
            F:=PrimitiveElement(K);
            q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
            _,p:=IsPrimePower(q);
            V:=q/F;
            R:=Order([F,V]);
            if exists{S:S in OverOrders(R)|not IsConjugateStable(S)} then
                h;
            end if;
    //        Ns:=[2,4,8,16,32,2*3,2*3*5,4*9];
    //        for N in Ns do
    //            vert,edges:=IsogenyGraphBuilder_Naive(R,N);
    //            vert2,edges2:=IsogenyGraphBuilder_LessNaive(R,N);
    //            assert #vert2 eq #vert;
    //            assert Keys(edges) eq Keys(edges2);
    //            assert forall{d:d in Keys(edges) | #edges[d] eq #edges2[d]};
    //            vert3,edges3:=IsogenyGraphBuilder(R,N);
    //            assert #vert3 eq #vert;
    //            assert Keys(edges) eq Keys(edges3);
    //            assert forall{d:d in Keys(edges) | #edges[d] eq #edges3[d]};
    //        end for;
        end if;
    end for;

// issue for x^2 - 2*x + 5 - solved after introducing O2^*/(O1^*O3^* meet O2^*)
h:=x^4 - x^2 + 4;
K:=EtaleAlgebra(f);
N := 2;
F:=PrimitiveElement(K);
V:=q/F;
R:=Order([F,V]);
vert3,edges3:=IsogenyGraphBuilder(R,N);
E := edges3[2];
WW := {x[1][1] : x in E};
#WW;

we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
WWW := [w : w in WW | ComplexConjugate(we_map(w)) @@ we_map ne w];
#WWW;


function find_example(N)
    Attach("IsogenyGraphBuilders.m");
    all:=Split(Read("weil_poly_sqfree_ord.txt"));
    PP<x>:=PolynomialRing(Integers());
    for c in all do
        h:=PP!eval(c);
        if Degree(h) eq 4 then
            K:=EtaleAlgebra(h);
            F:=PrimitiveElement(K);
            q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
            _,p:=IsPrimePower(q);
            V:=q/F;
            R:=Order([F,V]);
            Ss := {{S, ComplexConjugate(S)} : S in OverOrders(R)};
            Ss := {Representative(pair) : pair in Ss | #pair eq 2};
            if #Ss gt 0 then
                print "Checking", h;
                we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
                icm,icm_map:=IdealClassMonoidAbstract(R);
                WW := Classes(we);
                PR,pR := PicardGroup(R);
                for s in WW do
                    S := MultiplicatorRing(s);
                    if S in Ss then
                        t := ComplexConjugate(we_map(s))@@we_map;
                        T := MultiplicatorRing(t);
                        eS := ExtensionHomPicardGroups(R,S);
                        eT := ExtensionHomPicardGroups(R,T);
                        kS := Kernel(eS);
                        kT := Kernel(eT);
                        if kS ne kT then
                            Ws := we_map(s);
                            Wsdual := TraceDualIdeal(ComplexConjugate(Ws));
                            Wt := we_map(t);
                            Wtdual := TraceDualIdeal(ComplexConjugate(Wt));
                            //J := ColonIdeal(Wsdual, Wt);
                            J := ColonIdeal(Wtdual, Ws);
                            JJ := PicClass(J @@ icm_map);
                            JJbar := PicClass(ComplexConjugate(J) @@ icm_map);
                            Ms := [M : M in IntermediateIdeals(Wt,N*Wt) | M @@ we_map eq s];
                            for M in Ms do
                                source_M := M@@icm_map;
                                assert WEClass(source_M) eq s;
                                //aabarinv := -PicClass(ComplexConjugate(M)@@icm_map);
                                aabar := PicClass(ComplexConjugate(M)@@icm_map);
                                aainv := -PicClass(M@@icm_map);
                                Jai := JJ + aainv;
                                Jab := JJbar + aabar;
                                for b in PR do
                                    if eS(b) eq Jai and eT(b) ne Jab then
                                        return <h,s,M,b,t,PR,pR,eS,eT,kS,kT,R,S,T,Ws,Wsdual,Wt,J,JJ,b,bbar,aabarinv,Jai,Jab,we,we_map,icm,icm_map>;
                                    end if;
                                end for;
                                /*for b in PR do
                                    bbar := ComplexConjugate(pR(b))@@pR;
                                    if eT(b + bbar) eq Jai then
                                        return <h,s,M,b,t,PR,pR,eS,eT,kS,kT,R,S,T,Ws,Wsdual,Wt,J,JJ,b,bbar,aabarinv,Jai,we,we_map,icm,icm_map>;
                                    end if;
                                end for;*/
                            end for;
                        end if;
                    end if;
                end for;
            end if;
        end if;
    end for;
end function;
