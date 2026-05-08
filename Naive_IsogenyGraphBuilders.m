/*
    The intrinsic belows are preliminary versions of the algorithm
    to compute the D-isogeny graph. They are slower but less 
    sophisticated than the version contained in IsogenyGraphBuilder.m
    and presented in the paper. They are kept for testing purposes.

    IsogenyGraphBuilder_Naive loops over all of ICM(R) and constructs 
    all isogenies to each vertex.

    IsogenyGraphBuilder_LessNaive loops over the weak equivalence 
    class monoid of R, and uses the Pic action to construct all isogenies
    to each vertex.
*/

import "IsogenyGraphBuilder.m" : compute_orbits_UT_on_Ms;

intrinsic IsogenyGraphBuilder_Naive(R::AlgEtQOrd,D::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer D, returns the D-isogeny graph, given as a pair classes,edges:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the D-isogeny graph.
- edges is an associative array, indexed by positive integers d. 
  edges[d] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of isogenies of degree d in the following way:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}
    icm,icm_map:=IdealClassMonoidAbstract(R);
    classes:=Classes(icm);
    edges:=AssociativeArray(:Default:=[]);
    // edges is a 1-dimensional array
    // edges[d] contains the sequence of labels of isogenies of degree d.
    for target in classes do 
        IV:=icm_map(target); //IV is a representative of each vertex, chosen once and for all
        // Ms:=[M:M in IntermediateIdeals(IV,D*IV)|ind ne 1 and D mod ind eq 0 where ind:=Index(IV,M)]; //sub-frac.R-ideals M<IV s.t. [IV:M]|D
        Ms:=SubIdealsOfIndexDividing(IV,D); //sub-frac.R-ideals M<IV s.t. [IV:M]|D
        T:=MultiplicatorRing(IV);
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            d:=Index(IV,M);
            source:=icm!M;
            IV1:=icm_map(source); //this is chosen once and for all
            test,x:=IsIsomorphic(M,IV1); //x*IV1 = M 
            assert test; // sanity check
            Append(~edges[d],<[* WEClass(source),PicClass(source) *],[* WEClass(target),PicClass(target) *],IV1,IV,x>);
        end for;
    end for;
    return [[* WEClass(target),PicClass(target) *]:target in classes],edges;
end intrinsic;

intrinsic IsogenyGraphBuilder_LessNaive(R::AlgEtQOrd,D::RngIntElt) -> .
{Given the Frobenius order R of a squarefree ordinary isogeny class and a positive integer D, returns the D-isogeny graph, given as a pair classes,edges:
- classes is a sequence of lists [*W,L*] where W is a weak equivalence class (type AlgEtQWECMElt), and L is an element of an abstract group representing Pic(T) where T is the multiplicator ring of W. They represent the vertices of the D-isogeny graph.
- edges is an associative array, indexed by positive integers d. 
  edges[d] is a sequence of tuples <[*Ws,Ls*],[*Wt,Lt*],Is,It,x> each one representing an equivalence classes of isogenies of degree d in the following way:
  -- [*Ws,Ls*] and [*Wt,Lt*] are the elements in classes representing source and target, respectively.
  -- Is and It are fractional Z[F,V]-ideals representing the ideal classes of the source and target.
  -- x is an element of Q[F] giving an inclusion x*Is < It such that [It:x*Is]=d.}
    we,we_map:=WeakEquivalenceClassMonoidAbstract(R);
    icm,icm_map:=IdealClassMonoidAbstract(R);
    PR,pR:=PicardGroup(R);

    classes:=[ ];
    edges:=AssociativeArray(:Default:=[]);
    // edges is a 1-dimensional array
    // edges[d] contains the sequence of labels of isogenies of degree d.
    for t in Classes(we) do 
        T:=MultiplicatorRing(t);
        eT:=ExtensionHomPicardGroupsOverOrders(R,T);
        PT:=PicardGroup(T);
        for bbT in PT do
            Append(~classes,[* t,bbT *]);
        end for;
        Wt:=we_map(t);
        Ms:=SubIdealsOfIndexDividing(Wt,D); //sub-frac.R-ideals M<Wt s.t. [Wt:M]|D
        assert not Wt in Ms;
        Ms:=compute_orbits_UT_on_Ms(T,Ms,R);
        for M in Ms do
            d:=Index(Wt,M);
            source_M:=M@@icm_map;
            s:=WEClass(source_M);
            aaS:=PicClass(source_M);
            S:=MultiplicatorRing(s);
            Ws:=we_map(s);
            eS:=ExtensionHomPicardGroupsOverOrders(R,S);
            aa:=aaS@@eS; // in Pic(R);
            Iaa:=pR(aa);
            test,x:=IsIsomorphic(M,Ws*Iaa);
            assert test; // sanity check
            for bbT in PT do
                bb:=bbT@@eT;
                Ibb:=pR(bb);
                Append(~edges[d],<[* s,aaS *],[* t,bbT *],Ws*Iaa*Ibb,Wt*Ibb,x>);
            end for;
        end for;
    end for;
    return classes,edges;
end intrinsic;

