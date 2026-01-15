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
            if exists(S){S:S in OverOrders(R)|not IsConjugateStable(S)} then
                Sb:=ComplexConjugate(S);
                eS:=ExtensionHomPicardGroups(R,S);
                eSb:=ExtensionHomPicardGroups(R,Sb);
                if Kernel(eS) ne Kernel(eSb) then
                    h;
                end if;
            end if;
        end if;
    end for;
