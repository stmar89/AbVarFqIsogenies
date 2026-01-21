/*
    We collect here a series of quick tests used to test the various versions of
    IsogenyGraphBuilder against each other.
*/

    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");

    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    //f:=x^2 - 2*x + 5;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    Ns:=[2,4,8,16,32,2*3,2*3*5,4*9];

    //SetAssertions(2);

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
    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");
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
//
//after bug fixes
//N=  2, t=2.630, connected? false
//N=  4, t=3.090, connected? false
//N=  8, t=4.170, connected? false
//N= 16, t=6.300, connected? false
//N= 32, t=8.630, connected? false
//N=  6, t=5.380, connected? true
//N= 30, t=10.450, connected? true
//N= 36, t=13.310, connected? true
//N= 10, t=5.760, connected? true
//N= 15, t=4.650, connected? false
//
// after using myHash for keys in Assoc
//N=  2, t=2.460, connected? false
//N=  4, t=2.690, connected? false
//N=  8, t=2.830, connected? false
//N= 16, t=2.890, connected? false
//N= 32, t=3.430, connected? false
//N=  6, t=3.700, connected? true
//N= 30, t=6.730, connected? true
//N= 36, t=5.240, connected? true
//N= 10, t=5.260, connected? true
//N= 15, t=4.520, connected? false
//N= 15, t=4.140, connected? false
    
    // 3rd Algorithm, with Profiler.
    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^4-2*x^2+121;
    q:=Round(ConstantCoefficient(f)^(2/Degree(f)));
    K:=EtaleAlgebra(f);
    F:=PrimitiveElement(K);
    V:=q/F;
    R:=Order([F,V]);
    SetProfile(true);
    vert3,edges3:=IsogenyGraphBuilder(R,30);
    SetProfile(false);
    G:=ProfileGraph();
    ProfilePrintByTotalTime(G:Max:=10);

//
    issues:=[
    [ 729, 54, -11, 2, 1 ],
    [ 625, -25, 2, -1, 1 ],
    [ 4096, -192, 101, -3, 1 ],
    [ 4096, 320, 133, 5, 1 ],
    [ 4096, 768, 97, 12, 1 ],
    [ 1681, 410, 67, 10, 1 ]
    ];
    AttachSpec("~/AbVarFq_Isogenies_Private/magma/spec");
    PP<x>:=PolynomialRing(Integers());

    for c in issues do
        h:=PP!c;
        K:=EtaleAlgebra(h);
        F:=PrimitiveElement(K);
        q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
        V:=q/F;
        R:=Order([F,V]);
        Ns:=[2,4,8,16,32,2*3,2*3*5,4*9];
        tests:=[];
        for N in Ns do
            printf ".";
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
            Append(~tests,good);
        end for;
        if &and(tests) then
            printf "\nall good for %o\n",h;
        else
            printf "\nISSUE found for %o\t%o\n",h,tests;
        end if;
    end for;

