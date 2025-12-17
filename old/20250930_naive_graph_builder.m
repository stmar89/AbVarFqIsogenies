    // WARNING TODO some of the edges below might be equivalent!


    SetColumns(0);

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");

    N:=8;
    label:="2.13.d_y";


    divs:=Exclude(Divisors(N),1);
    g,q,h:=LabelToPoly(label);

    // Given an isogeny class isog over Fq, and a positive integer N returns the graph consisting of all isogenies
    // between the isomorphism classes.
    R:=ZFVOrder(IsogenyClass(h));
    P,p:=PicardGroup(R);
    icm,map:=IdealClassMonoidAbstract(R);
    gens:=[p(P.i)@@map:i in [1..Ngens(P)]];
    classes:=Classes(icm);

    printf "Picard group of ZFV:\n";
    P;

    printf "image of the action of each generator of Pic on element of icm:\n";
    for g in gens do  
        [ Index(classes,g*c) : c in classes ];
    end for;

    edges:=AssociativeArray();
    for d in divs do
        edges[d]:=[];
    end for;

    for i in [1..#classes] do
            I:=map(classes[i]);
            ids:=&cat[IdealsOfIndex(I,n):n in divs]; 
            for K in ids do
                for j in [1..#classes] do
                    J:=map(classes[j]);
                    test,x:=IsIsomorphic(K,J); //K = xJ    
                    if test then
                        assert x*J eq K; //I always get confused about the order
                        d:=Index(I,K);
                        Append(~edges[d],<j,i>);
                        break j;
                    end if;
                end for;
            end for;
    end for;

    printf "vertices = %o\n",[1..#classes];
    for d->ed in edges do
        printf "edges of degree %o = %o\n",d,ed;
    end for;
