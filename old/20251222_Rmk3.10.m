PP<x>:=PolynomialRing(Integers());
all:=Split(Read("~/AbVarFq_Isogenies_Private/magma/weil_poly_sqfree_ord.txt"));
tot:=#all; perc:=0;
for icc->cc in all do
    if Truncate(100*icc/tot) gt perc then perc+:=1; printf "%o%% ",perc; end if;
    h:=PP!eval(cc);
    K:=EtaleAlgebra(h);
    F:=PrimitiveElement(K);
    q:=Round(ConstantCoefficient(h)^(2/Degree(h)));
    R:=Order([F,q/F]);
    ff:=Conductor(R);
    pp:=PrimesAbove(ff);
    O:=MaximalOrder(K);
    for P in pp do
        if MultiplicatorRing(P) eq O then
            Ls:=IntermediateIdeals(P,P^2,O:PrescribedMultiplicatorRing:=true);
            Ls:=[L:L in Ls | IsInvertible(L)];
            assert forall{L:L in Ls | O!!L eq O!!P};
            if #Ls eq 0 then
                h;
            end if;
        end if;
    end for;
end for;




