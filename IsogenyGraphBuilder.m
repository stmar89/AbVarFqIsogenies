/*
    This file contains the main algorithms to compute the N-isogeny graph.
    The first MinimalIsogenyGraphBuilder computes only the minimal edges.
    The second one, IsogenyGraphBuilder, uses the first and then constructs
    all compositions of degree dividing N.
*/

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

intrinsic IsogenyGraphBuilder(R::AlgEtQOrd,N::RngIntElt) -> SeqEnum,Assoc
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
                target:=myHash(label[4]);
                source:=myHash(label[3]);
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
                    target_E2:=myHash(E2[4]);
                    // REMOVE?
                    if not IsDefined(edges[n],target_E2) then edges[n][target_E2]:=AssociativeArray(); end if;
                    // now, we loop over all already computed edges E1 of degree d1=n/d2 such
                    // that target(E1) = source(E2) = E2[3], since we want to construct the composition E2*E1
                    // (first apply the isogeny E1 then the isogeny E2)
                    source_E2:=myHash(E2[3]);
                    if IsDefined(edges,d1) and IsDefined(edges[d1],source_E2) then
                        for E1_t->E1s in edges[d1][source_E2] do
                            for E1 in E1s do
                                source_E1:=myHash(E1[3]);
                                //REMOVE?
                                if not IsDefined(edges[n][target_E2],source_E1) then edges[n][target_E2][source_E1]:=[]; end if;
                                O1:=MultiplicatorRing(E1[3]); // mult ring of source(E1)
                                O2:=MultiplicatorRing(E1[4]); // mult ring of target(E1)=source(E2)
                                O3:=MultiplicatorRing(E2[4]); // mult ring of target(E2)
                                U:=QuotientOfJoinUnitsOverOrders(R,O1,O2,O3);
                                LU:=[];
                                for u in U do
                                    Ecomp:=<E1[1],E2[2],E1[3],E2[4],E1[5]*u*E2[5]>;
                                    if not exists{E:E in edges[n][target_E2][source_E1]|
                                        AreIsogeniesEquivalent(Ecomp[5],E[5],E[3],E[4])} then
                                        Append(~LU,Ecomp);
                                    end if;
                                end for;
                                edges[n][target_E2][source_E1] cat:=LU;
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
                // the following assert is very time consuming
                assert2 forall{i:i in [1..#edges_d_t_s]|not exists{j:j in [1..i-1]|
                               AreIsogeniesEquivalent(Ei[5],Ei[3],Ei[4],Ej[5],Ej[3],Ej[4]) 
                               where Ei:=edges_d_t_s[i] where Ej:=edges_d_t_s[j]}};
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
   
    Attach("~/AbVarFq_Isogenies_Private/magma/IsogenyGraphBuilders.m");

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
N=  2, t=2.460, connected? false
N=  4, t=2.690, connected? false
N=  8, t=2.830, connected? false
N= 16, t=2.890, connected? false
N= 32, t=3.430, connected? false
N=  6, t=3.700, connected? true
N= 30, t=6.730, connected? true
N= 36, t=5.240, connected? true
N= 10, t=5.260, connected? true
N= 15, t=4.520, connected? false
N= 15, t=4.140, connected? false
    
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
    vert3,edges3:=IsogenyGraphBuilder(R,30);
    SetProfile(false);
    G:=ProfileGraph();
    ProfilePrintByTotalTime(G:Max:=10);



*/


