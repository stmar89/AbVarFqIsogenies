// testing various versions of the algorithm
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    all:=Split(Read("weil_poly_sqfree_ord.txt"));
    PP<x>:=PolynomialRing(Integers());
    for c in all do
        h:=PP!eval(c);
        h;
        K:=EtaleAlgebra(h);
        F:=PrimitiveElement(K);
        q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
        _,p:=IsPrimePower(q);
        V:=q/F;
        R:=Order([F,V]);
        Ns:=[2,4,8,16,32,2*3,2*3*5,4*9];
        for N in Ns do
            vert,edges:=IsogenyGraphBuilder_Naive(R,N);
            vert2,edges2:=IsogenyGraphBuilder_LessNaive(R,N);
            assert #vert2 eq #vert;
            assert Keys(edges) eq Keys(edges2);
            assert forall{d:d in Keys(edges) | #edges[d] eq #edges2[d]};
            vert3,edges3:=IsogenyGraphBuilder(R,N);
            assert #vert3 eq #vert;
            assert Keys(edges) eq Keys(edges3);
            assert forall{d:d in Keys(edges) | #edges[d] eq #edges3[d]};
        end for;
    end for;

// issue for x^2 - 2*x + 5 - solved after introducing O2^*/(O1^*O3^* meet O2^*)
