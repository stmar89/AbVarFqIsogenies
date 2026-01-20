/*
    This file contains intrinisc to test equivalence between 
    isogenies represented by includsions of the form x*I < J, 
    where I,J are fractional ideals over the Frobenius order.
*/

intrinsic AreIsogeniesEquivalent(x1::AlgEtQElt, I1::AlgEtQIdl, J1::AlgEtQIdl, x2::AlgEtQElt, I2::AlgEtQIdl, J2::AlgEtQIdl) -> BoolElt
{Given inclusions x1*I1<J1 and x2*I2<J2 of fractional ideals of the Frobenius order representing isogenies, return whether they are equivalent.}
    K:=Algebra(I1);
    one:=One(K);
    if I1 eq I2 then
        y:=one;
    else
        test,y:=IsIsomorphic(I1,I2); // I1=y*I2
        if not test then
            return false;
        end if;
    end if;
    if J1 eq J2 then
        z:=one;
    else
        test,z:=IsIsomorphic(J1,J2); // J1=z*J2
        if not test then
            return false;
        end if;
    end if;
    elt:=((x1*y)/(x2*z));
    inv:=1/elt;
    S:=MultiplicatorRing(I1);
    T:=MultiplicatorRing(J1);
    R:=Order(I1);
    if InclusionOverorders(R,S,T) then
        return elt in T and inv in T;
    elif InclusionOverorders(R,T,S) then
        return elt in S and inv in S;
    end if;
    OK:=MaximalOrder(K);
    if inv notin OK then
        return false;
    end if;
    _,uOK:=UnitGroup(OK);
    U:=JoinUnitsOverorders(R,S,T); // U = S^*T^* as a subgroup of OK^*
    return (elt@@uOK) in U;
end intrinsic;

intrinsic AreIsogeniesEquivalent(x1::AlgEtQElt, x2::AlgEtQElt, I::AlgEtQIdl, J::AlgEtQIdl)->BoolElt
{Given inclusions x1*I<J and x2*I<J of fractional ideals of the Frobenius order representing isogenies, return whether they are equivalent.}
    K:=Algebra(I);
    one:=One(K);
    elt:=x1/x2;
    inv:=1/elt;
    S:=MultiplicatorRing(I);
    T:=MultiplicatorRing(J);
    R:=Order(I);
    if InclusionOverorders(R,S,T) then
        return elt in T and inv in T;
    elif InclusionOverorders(R,T,S) then
        return elt in S and inv in S;
    end if;
    OK:=MaximalOrder(K);
    if elt notin OK or inv notin OK then
        return false;
    end if;
    _,uOK:=UnitGroup(OK);
    U:=JoinUnitsOverorders(R,S,T); // U = S^*T^* as a subgroup of OK^*
    return (elt@@uOK) in U;
end intrinsic;
