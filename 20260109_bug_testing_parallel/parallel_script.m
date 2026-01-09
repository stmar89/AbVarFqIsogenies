// testing various versions of the algorithm

// WARNING: do not forget to remove the issue file after a fix
// parallel -j 20 --resume --timeout 600 --joblog ~/AbVarFq_Isogenies_Private/magma/20260109_bug_testing_parallel/joblog -a ~/AbVarFq_Isogenies_Private/magma/weil_poly_sqfree_ord.txt magma -b c:={} ~/AbVarFq_Isogenies_Private/magma/20260109_bug_testing_parallel/parallel_script.m

    issue_file:="~/AbVarFq_Isogenies_Private/magma/20260109_bug_testing_parallel/issues.txt";
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");
    PP<x>:=PolynomialRing(Integers());
    h:=PP!eval(c);
    h;
    K:=EtaleAlgebra(h);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    V:=q/F;
    R:=Order([F,V]);
    Ns:=[2,4,8,16,32,2*3,2*3*5,4*9];
    for N in Ns do
        vert,edges:=IsogenyGraphBuilder_Naive(R,N);
        vert2,edges2:=IsogenyGraphBuilder_LessNaive(R,N);
        vert3,edges3:=IsogenyGraphBuilder(R,N);
        good:=
            #vert2 eq #vert and
            Keys(edges) eq Keys(edges2) and
            forall{d:d in Keys(edges) | #edges[d] eq #edges2[d]} and
            #vert3 eq #vert and
            Keys(edges) eq Keys(edges3) and
            forall{d:d in Keys(edges) | #edges[d] eq #edges3[d]};
        if not good then
            fprintf issue_file,"%o\n",c;
        end if;
    end for;

// issue for x^2 - 2*x + 5 - solved after introducing O2^*/(O1^*O3^* meet O2^*)
