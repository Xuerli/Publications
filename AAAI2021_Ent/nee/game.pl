:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].


axiom([-mark(\x, \y),-box(\y), +select(\x,\y)]).
axiom([+fewer(g1,hp,hm)]).
axiom([+fewer(g2,hm,hp)]).
axiom([+mark(g1,b1)]).
axiom([+mark(g2,b1)]).
axiom([+box(b1)]).
axiom([+box(b2)]).
axiom([+box(b3)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([select(g1,b1), select(g2,b2), select(g2,b3)]).
falseSet([select(g1,b2), select(g1,b3), select(g2,b1)]).
%
protect([]).
heuristics([noEE]).
theoryFile:- !.
