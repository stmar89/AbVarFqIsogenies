intrinsic GraphOverOrders0(R:AlgEtQOrd)->GrphDir
{
This is a replacement for https://magma.maths.usyd.edu.au/magma/handbook/text/455#4979 which is slower. 
Given an order R returns the graph G of minimal inclusions of the overorders of R. More precisely, the vertices of G are integers between 1 and the number of OverOrders(R), and there is an edge [i, j] if and only if OverOrders(R)[j] is a minimal overorder of OverOrders(R)[i].
}
    ords:=OverOrders(R);
    pairs:=[[i,j] : i in [1..#ords], j in [1..#ords] | i ne j];
    subs:=[];
    for pair in pairs do
        i,j:=Explode(pair);
        Oi:=ords[i];
        Oj:=ords[j];
        if Oi subset Oj then
            Append(~subs,pair);
        end if;
    end for; 
    
    function is_primitive(pair)
        i,j:=Explode(pair);
        return not exists(k){ k : k in [1..#ords] | [i,k] in subs and [k,j] in subs };
    end function;
    
    edges:=[ pair : pair in subs | is_primitive(pair)];
    return Digraph<#ords|edges>;
end intrinsic;


////////////////////
// Weil Polynomial Intrinsics
////////////////////

function Base26Encode(n)
        alphabet := "abcdefghijklmnopqrstuvwxyz";
        s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
        while n gt 0 do
                s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
        end while;
        return s;
end function;


intrinsic IsogenyLabel(f::RngUPolElt)->MonStgElt
{returns the LMFDB label of the isogeny class determined by a Weil polynomial f.}
    g:=Degree(f) div 2;
    q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
    str1:=Reverse(Prune(Coefficients(f)))[1..g];
    str2:="";
    for a in str1 do
        if a lt 0 then
            str2:=str2 cat "a" cat Base26Encode(-a) cat "_";
            else
            str2:=str2 cat Base26Encode(a) cat "_";
        end if;
    end for;
    str2:=Prune(str2);
    isog_label:=Sprintf("%o.%o.",g,q) cat str2;
    return isog_label;
end intrinsic;


intrinsic WeilPolynomial(L:RngUPolElt)->RngUPolElt
{Convert an L-polynomial of an abelian variety to an P-polynomial (characteristic polynomial of the Frobenius). It does no testing.}
    P:=Parent(L);
    x:=P.1;
    g:=Z!(Degree(L)/2);
    f:=P!(x^(2*g)*Evaluate(L,1/x));
    return f;
end intrinsic;

intrinsic Getgqp(f::RngUPolElt)->RngIntElt,RngIntElt,RngIntElt
{Given a Weil polynomial of an abelian variety determine the g, the dimension, q, cardinality of the base field, p, the characteristic of the base field.
This does no testing if the element f is actually a Weil polynomial.}
    bool,p,r:=IsPrimePower(ConstantCoefficient(f));
    g:=Z!(Degree(f)/2);
    s:=Z!(r/g);
    q:=p^s;
    return g,q,p;
end intrinsic;

intrinsic WeilBaseChange(f::RngUPolElt,r::RngIntElt)->RngUPolElt
{Given a Weil polynomial over an abelian variety over a finite field with q elements and an integer r compute the Weil polynomial of the abelian variety of the abelian variety base changed to the field with q^r elements.}
    P:=Parent(f);
    x:=P.1;
    P1<y,u>:=PolynomialRing(Z,2);
    ff:=Evaluate(f,u);
    f2:=Resultant(u^r-y,ff,u);
    f2:=P!Evaluate(f2,[x,0]);
    return f2;
end intrinsic;

