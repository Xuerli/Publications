:- working_directory(_, '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/').
:-[main].


axiom([-student(\x),+notworking(\x)]).
axiom([-undstudent(\x),+student(\x)]).
axiom([-undstudent(\x),+adult(\x)]).
axiom([-adult(\x),+working(\x)]).
axiom([+undstudent(lily)]).
axiom([-working(\x),-notworking(\x)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([undstudent(lily),  working(lily)]).
falseSet([]).
%
protect([]).
heuristics([]).
theoryFile:- !.
