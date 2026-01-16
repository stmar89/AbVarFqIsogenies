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

intrinsic MinimalIsogenyGraphBuilder(R::AlgEtQOrd,N::RngIntElt) -> SeqEnum,Assoc
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the minimal N-isogeny graph, given as a pair classes,edges_min:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the N-isogeny graph.
- edges is a 3-dimensional associative array:
  edges[d][myHash(It)][myHash(Is)] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of minimal isogenies of degree d from Is to It as follows:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}

    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    classes:=[ ];
    edges:=AssociativeArray();
    // a 3 dimensional array: edges[d][T][S] where
    // - d is a positive integer (dividing N)
    // - T,S are distinguished ideals representing an ideal classes
    // is the sequence of labels of isogenies of degree d from S to T

    // Some if-statements in this intrinsic and in the next ones could be omitted if I could  
    // define edges with 'nested' Defaults, as in the next line. This does not work in 2.29-4. 
    // edges:=AssociativeArray(:Default:=AssociativeArray(:Default:=AssociativeArray(:Default:=[])));
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
    return classes,edges;
end intrinsic;

intrinsic IsogenyGraphBuilder(R::AlgEtQOrd,N::RngIntElt) -> SeqEnum,Assoc
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer N, returns the N-isogeny graph, given as a pair classes,edges:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the N-isogeny graph.
- edges is an associative array, indexed by positive integers d dividing N. 
  edges[d] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of isogenies of degree d in the following way:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}

    classes,edges:=MinimalIsogenyGraphBuilder(R,N);
    edges_min:=AssociativeArray(:Default:=[]);
    // We collapse the 3-dimensional array edges into a 1-dimensional array to simplify
    // the nested loops below. So: edges_min[d] is the sequence of minimal isogenies of degree d
    for d->edges_d in edges do
        edges_min_d:=[];
        for t->edges_d_t in edges[d] do
            for s->edges_d_t_s in edges[d][t] do
                // the following assert is very time consuming
                assert2 forall{i:i in [1..#edges_d_t_s]|not exists{j:j in [1..i-1]|
                               AreIsogeniesEquivalent(Ei[5],Ei[3],Ei[4],Ej[5],Ej[3],Ej[4]) 
                               where Ei:=edges_d_t_s[i] where Ej:=edges_d_t_s[j]}};
                edges_min_d cat:=edges_d_t_s;
            end for;
        end for;
        if #edges_min_d gt 0 then
            edges_min[d]:=edges_min_d;
        end if;
    end for;

    // The 3-dimensional array edges contains only minimal edges so far, which are also copied in the 
    // 1-dimensional array edges_min. We create all possible compositions of degree dividing N and 
    // add them to the array edges.
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
                    if not IsDefined(edges[n],target_E2) then edges[n][target_E2]:=AssociativeArray(); end if;
                    // now, we loop over all already computed edges E1 of degree d1=n/d2 such
                    // that target(E1) = source(E2) = E2[3], since we want to construct the composition E2*E1
                    // (first apply the isogeny E1 then the isogeny E2)
                    source_E2:=myHash(E2[3]);
                    if IsDefined(edges,d1) and IsDefined(edges[d1],source_E2) then
                        for E1_t->E1s in edges[d1][source_E2] do
                            for E1 in E1s do
                                source_E1:=myHash(E1[3]);
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

    // We transforms the output from the 3-dimensional array edges (with keys described as in
    // the intrinsic MinimalIsogenyGraphBuilder) to a 1-dimensioanl array edges_output index 
    // only by degrees d dividing the input N.
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
