:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].



axiom([+penguin(tweety)]).
axiom([+bird(polly)]).
axiom([-bird(\x), +fly(\x)]).
axiom([-penguin(\y), +bird(\y)]).
axiom([-bird(\y), +feather(\y)]).


trueSet([feather(tweety),feather(tweety), fly(bird)]).
falseSet([fly(tweety)]).






protect([]).
heuristics([noEE]).
theoryFile:- !.
