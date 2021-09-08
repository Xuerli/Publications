:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].



axiom([+hasCar(car1)]).
axiom([+hasCar(car2)]).
axiom([+hasCar(car3)]).
axiom([+hasCar(car4)]).
axiom([+boxShape(load1)]).
axiom([+boxShape(load3)]).
axiom([+notboxShape(load2)]).
axiom([+hasLoad(car1,load1)]).
axiom([+hasLoad(car2,load2)]).
axiom([+hasLoad(car4,load3)]).
axiom([-notboxShape(\x), -boxShape(\x)]).

trueSet([eastBound(car1),eastBound(car4)]).
falseSet([eastBound(load1),eastBound(car2),eastBound(car3)]).

protect([]).
heuristics([noEE]).
theoryFile:- !.
