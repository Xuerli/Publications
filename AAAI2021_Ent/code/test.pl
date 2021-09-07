trueSet([match(aId2, bId2),match(aId3, bId3)]).
falseSet([match(aId1, bId1)]).
heuristics([noRuleChange,noReform]).     %noAxiomAdd %noAxiomDele noArityChange noReform noPrecAdd, noPrecDele, noRuleChange, noAss2Rule, noAnalogy
protect([[+match(\x, \y), -range(\x, \y, in), -databaseA(\x), -databaseB(\y)],range,databaseB,databaseA, asst(databaseA), asst(databaseB)]).        %protect predicate name swan and its arity from being changed.



axiom([+match(\x, \y), -range(\x, \y, in), -databaseA(\x), -databaseB(\y)]).
axiom([+databaseA(aId1)]).
axiom([+databaseB(bId1)]).
axiom([+range(aId1, bId1, in)]).
axiom([+databaseA(aId2)]).
axiom([+databaseB(bId2)]).
axiom([+range(aId2, bId2, in)]).
axiom([+databaseA(aId3)]).
axiom([+databaseB(bId3)]).
axiom([+range(aId3, bId3, in)]).