:- working_directory(_, '/Users/lixue/GoogleDrive/publish/ACS/code').
:-[main].

axiom([+parent(a,b,birth)]).
axiom([+parent(a,c,step)]).
axiom([+parent(c,d,birth)]).
axiom([+parent(e,g,birth)]).
axiom([+families(\x,\y), -parent(\x,\y,birth)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Preferred Structure:

trueSet([families(a,b),families(a,c),families(c,d),families(e,g)]).
falseSet([]).
protect([]).
heuristics([]).

theoryFile:- pass.
