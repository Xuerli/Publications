
%% ABC Repair System Procedure %%
%% Xue Li Feb 2019 %%

%% This file contains the functions/predicates of dealing with proofs.
:- [reform].
/**********************************************************************************************************************
    slRL((Goal, Ancestors), TheoryIn, Proofs, Evidence, Record): SL resolution based on reputation.
    Input:  (Goal, Ancestors): Goal is the main goal, which could be a list of subgoals.
             Ancestors is the ancestor resolutions which produces Goals.
             TheoryIn is the input theory;
            * CAUTION: each input clause is a Horn clause with its HEAD IN FRONT.
    Output: either a Proof of Goal or an evidence of a failed proof, and the other is [].
            Record: A record in the form of (Goal, AxiomsList):
                    Goal is the proposition that proves by the proofs;
                    AxiomsList is a list of axioms that construct the proof/the evidence.
        CAUTION: In a failed proof, it is the first subgoal cannot be resolved.
        Example of a Proof: ([], ([-[german,[bruce]]],([-[european,[bruce]]],([-[swan,[bruce]],-[european,[bruce]]],([-[white,[bruce]]],falseSet),[+[white,vble(x)],-[swan,vble(x)],-[european,vble(x)]],[]),[+[swan,[bruce]]],[]),[+[european,vble(x)],-[german,vble(x)]],[]),[+[german,[bruce]]],[])
        The tree of this proof is:
        ([],
            ([-[german,[bruce]]],
                ([-[european,[bruce]]],
                          ([-[swan,[bruce]],-[european,[bruce]]],
                                  ([-[white,[bruce]]],falseSet),
                                  [+[white,vble(x)],-[swan,vble(x)],-[european,vble(x)]],[]),
                          [+[swan,[bruce]]],[]),
                [+[european,vble(x)],-[german,vble(x)]],[]),
            [+[german,[bruce]]],[])
        Example of a proof of an equality:([+[=,[a],[b]],.....).
************************************************************************************************************************/
% Rewrite the input goal and the theory.
slRL((Goal, Ancestors), TheoryIn, Proof, Evidence, Theorem, AxiomsList):-!,
    % Set an depth limit of the resoluton according to the length of the thoery.
    length(TheoryIn, L),
    RLimit is L*L,    % the depth limit of a proof.
    % move the head of a rule in the front and the equality/inequality literals in the end of each body.
    appEach(orderAxiom, TheoryIn, TheoryTem),
      % if there is a head in the goal clause, then move the head to the end, which is for the derivation of an assertion theorem.
    (member(+Head, Goal) -> delete(Goal, +Head, RestGoal), 
                            append(RestGoal, [+Head], GoalNew),!; 
                            GoalNew = Goal),
    slRLMain((GoalNew, Ancestors), Deriv, TheoryTem, Proof, Evidence, Theorem, RLimit).
    
%% slRLMain1: No goals remain to resolve, a theorem is found, output the whole proof ([], Ancestors).
% When a proof is found, do not search further, and the evidence of partial proof is empty.
slRLMain([+Literal], Proof, _, Proof, [], Theorem, RCostLimit):-
    Theorem = [+Literal],
    !, assert((proofStatus, 0).  
    
%% slRLMain2: No goals to resolve, output the whole proof ([], Ancestors) with [] for Evidence and Theorem.
% When a proof is found, do not search further
slRLMain([], Proof, _, Proof, [], [], _):-
    !, assert((proofStatus, 0).                                    % The proof is output. Reset the proofStatus to the default value 0.

%% slRLMain3: Use an input clause to resolve Goal which does not have == as its predicate.
slRLMain(Goals, Deriv, TheoryIn, Proof, Evidence, Theorem, RCostLimit):-
    Goals = [-[Pred| _]| _],                                  % get the predicate of the left most sub-goal to resolve.
    %**Caution: any CUT here will cause the issue of unable to find all proofs even under findall/3. Therefore, a Flag proofStatus is applied.
    assert((proofStatus, 1),                                    % Set the proofStatus as 1, which says an input axiom will be picked for the resoltuion.
    length(Deriv, RDepth),
    RDepth =< RCostLimit,    % The current proof depth has not bigger than the limit.
    % Require that the head of a clause should be its first literal.
    InputClause = [+[Pred| Arg2]| Body],
    member((InputClause, Source), TheoryIn),             % Successfully get one input clause whose head has the same predicate with the predicate of the goal. % It could be a clause added by abduction
    % Do not resolve a goal with propositions from the preferred structure.
    \+ member(Source, [trueSet, falseSet]), 
    % rewrite shared the variable in Goals if that variable occurs both in the goal and the input clause.
    rewriteVble((Goals, Ans), InputClause, (GoalsTem, Ancestors)),
    GoalsTem = [-Goal| GoalsRest],
    reform(Goal, [Pred| Arg2], [], Substitution, success, success, []),        % If successful resolution
    append(Body, GoalsRest, GoalsTem2),                             % Get the resulting clause C with newly introduced literals Body in front.
    subst(Substitution, GoalsTem2, GoalsNew),
    \+ loopBack(GoalsNew, {GoalsTem, Ancestors}),         % The new goal clause do not cause a loop in the way of conaining a previous goal clause.
    %* Do not remove duplicated sub-goals which will effect trace-back process.
    assert((proofStatus, 0),                                    % Reset the proofStatus flag to the default value 0.
    % write_term([Goal| GoalsRest]), nl, write_term('input clause: '), write_term([+[Pred| Arg2]| Body]), nl,
    NewAncestors= {{GoalsTem, Ans}, InputClause, Source},          % Record the parents of this resolution by puting the goals in front and the input clause in the end.
    %write_term('New goals: '), write_term(GoalsNew), nl,
    RDepthNew is RDepth + 1,
    slRLMain({GoalsNew, NewAncestors}, TheoryIn, Proof, Evidence, Theorem, [InputClause| AxiomListIn], AxiomListOut, RDepthNew, RList). % Resolve the rest goals.


%% slRLMain4: When there is no input clause which can resolve the goal, or the depth of the partial proof is bigger than the search limit, 
%%                 return the evidence of the partial proof with [] as the proof and theorem.
%% Notice that only the first subgoal in Goals is gaurenteed to be unresolvable. The following subgoals could be resolvable.
slRLMain({Goals, Ancestors}, _, [], {Goals, Ancestors}, [], ClsList, ClsList, _, _):-
    nb_getval(proofStatus, 1),      % All axioms from the input theory have been tried for resolving the goal.
    Goals \= [],                    % And they all failed in resolving the remaining Goal.
    Goals \= [+_],                    % And it is not a derived assertion
    assert((proofStatus, 0).      \% The failed proof is output. Reset the proofStatus to the default value 0.


/**********************************************************************************************************************
    splitGoals(AllProofs, ProGoalsIn, ProGoalsOut, UnprGoalsIn, UnprGoalsOut):
            From Proofs, find the provable Goals with their proofs and the unprovable ones and their evidence of partial proofs.
            Partial proof is one which cannot be further resolved.
    Input:  AllProofs: It is a list of (Goal, ProofInfos),
                ProofInfos is a list of two sublists, where the first sublist is proofs and the second sublist is evidence of partial proofs.
            ProGoalsIn: an intern record of proved goals.
            UnprGoalsIn: an intern record of unprovable goals.
    Output: ProGoalsOut: the record of all proved goals with their proofs.
            e.g., ProGoalsOut = [([-[european,[bruce]]],[([],([-[european,[bruce]]],trueSet),[+[european,[bruce]]],[])]), ([-G2],[Proof1, Proof2...])...]
            UnprGoalsOut: the record of all unprovable goals with their failed proofs.
************************************************************************************************************************/
splitGoals([], ProGs, ProGs, UnpGs, UnpGs):- !.
splitGoals([(Goal, ProofInfos)| RestGP], ProGsIn, ProGsOut, UnpGsIn, UnpGsOut):-
    nth0(0, ProofInfos, Proofs),    % Get a list of proofs Proofs = [(P1,A1),(P2,A2),([],A3)], where A* is the list of axioms constituted that proof.
    % if there is no proof for this goal,
    (forall(member((P,_), Proofs), P = [])->
        nth0(1, AllProofs, Evidence),
        % If there is no complete proof, then the goal is insufficient, record its failed proofs.
        splitGoals(RestGP, ProGsIn, ProGsOut, [(Goal, Evidence) |UnpGsIn], UnpGsOut);
        % If there is complete proof(s), then ignore the failed one and record this sufficient Goal with its proofs.
        splitGoals(RestGP, [(Goal,Proofs)|ProGsIn], ProGsOut, UnpGsIn, UnpGsOut)).

/***************************************************************************************************************
    loopBack(GoalsCur, Proof):-
           Check if the current goals is more complex than a previous goal in its own Proof.
           If yes, return true, otherwise, return false.
Input:  GoalList is a list of goals, negative literals.
    Proof = {Goals, Ancestors}
           Example for a proof([],([-[german,[bruce]]],([-[european,[bruce]]],([-[swan,[bruce]],-[european,[bruce]]],([-[white,[bruce]]],falseSet),[+[white,vble(x)],-[swan,vble(x)],-[european,vble(x)]],[]),[+[swan,[bruce]]],[]),[+[european,vble(x)],-[german,vble(x)]],[]),[+[german,[bruce]]],[])
TODO: Consider different name of varibles.
    * InputClause is a Horn clause which has to have its positive literal as the head (in the begining of its list.
'/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/'
P= ([-[german,[bruce]]],([-[european,[bruce]]],([-[swan,[bruce]],-[european,[bruce]]],([-[white,[bruce]]],falseSet),[+[white,vble(x)],-[swan,vble(x)],-[european,vble(x)]],[]),[+[swan,[bruce]]],[]),[+[european,vble(x)],-[german,vble(x)]],[]), loopBack([-[swan,[bruce]],-[european,[bruce]]],P).
****************************************************************************************************************/
loopBack([],_):- fail,!.    % empty goal clause could not cause a loop.
loopBack(_,{[],_}):- !.     % a loop is found when there is already an empty goal clause.
% The current goal is more complicated than a previous goal if all of the previous subgoals can be resolved with a proposition in the current goal.
loopBack(GoalsCur, {GoalPar, _}):-
    writeLog([nl, write_term('---------------- Check if the current goal contains a previous goal------------'), nl,
            write_term('Current goal is: '), write_term(GoalsCur), nl, write_term('A previous goal is: '),write_term(GoalPar))),
    % For all the subgoal from the previous goal GoalPar, there is an subgoal in the currenct goal which resolves GoalPar.
    forall( member(-SGoal, GoalPar), 
            setof(SubGoal, 
                  (member(-SubGoal, GoalsCur),
                  reform(SGoal, SubGoal, [], _, fail, _, [])),
                  _)).
% check the previous goals in the ancestors.
loopBack(GoalsCur, {_, Ances}):-
    Ances = {{GoalsTem, Ancestors}, _, _},                                                                                  
    loopBack(GoalsCur, {GoalsTem, Ancestors}), !.

/***************************************************************************************************************
    traceBackPos(TgtProp, Proof, OutputPos, OutputNeg):
            Find the original clause which introduces the targeted proposition: TgtProp and the one which resolve TgtProp away.
    Input:  Proof is the proofs of the targeted literal.
            Proof = {{Goals, Ancestors1}, InpClause, InpClauseSource},
            Ancestors1 = {{[Goal2| GoalRest], Ancestors2}, InputClause2, InpClauseSource2)
            Goals are the remaining sub-goals after resolving Goal2 with InputClause2. Goals could be [];
            Ancestors2 are the ancestors resulting [Goal2| GoalRest].
    Output:
           OutputPos: (H, ClauseOri, Souc) is the positive literal which resolves the TgtProp away.
           OutputNeg is the negative literal which introduces TgtProp.
           ClauseOri: the original input clause which introduces the targeted literal.
           Souc is the source where the original clause comes from: [] for the input axiom, 'abduction' for added axiom.
           LitOrigNeg is the original negative literal which introduces the TgtSubGoal.
           LitOrigPos is the original positive literal
    * InputClause is a Horn clause which has its positive literal as the head.
****************************************************************************************************************/
% The targeted proposition is one in preferred structure.
traceBackPos(TgtProp, {_, Ances}, OutputPos, OutputNeg):-
    Ances = {{[-TgtProp], Source}, ClInput, SouCl},
    member(Source, [trueSet, falseSet, preferStruc]), !,
    ClInput = [HeadLiteral|_],
    OutputPos = (HeadLiteral, ClInput, SouCl),
    OutputNeg = (-TgtProp, [-TgtProp], Source).

% Find the positive literal.
traceBackPos(TgtProp, {_, Ances}, OutputPos, OutputNeg):-
    Ances = {{_, Ans1}, ClInput, Souc},
    ClInput = [+Head| _],
    reform2([TgtProp = Head],[],_,success,success,[])->
      OutputPos = (+Head, (ClInput, Souc)),
      traceBackNeg(TgtProp, Ans1, OutputNeg);
      traceBackPos(TgtProp, Ans1, OutputPos, OutputNeg).


/*---------------------------------------------------------------------------------------------------------------
    traceBackNeg(TgtProp, Ancestors, OutputNeg):
           Find the original negative literal and its input clause which introduces the targeted proposition: TgtProp.
    Input: Ancestors = ([Goal| GoalRest], Ancestors2, InputClause2)
           Goal is -TgtProp;
           Ancestors2 are the ancestors resulting [Goal| GoalRest].
           Example for a proof: ([],([-[german,[bruce]]],([-[european,[bruce]]],([-[swan,[bruce]],-[european,[bruce]]],([-[white,[bruce]]],falseSet),[+[white,vble(x)],-[swan,vble(x)],-[european,vble(x)]],[]),[+[swan,[bruce]]],[]),[+[european,vble(x)],-[german,vble(x)]],[]),[+[german,[bruce]]],[])
    Output: (LitOrigNeg, (ClauseOrig, SoucOrig))
           LitOrigNeg is the negative literal which introduces TgtProp.
           ClauseOrig: the original input clause which introduces LitOrigNeg.
           SoucOrig is the source where ClauseOrig comes from: [] for the input axiom, 'abduction' for added axiom.
    * ClauseOrig is a Horn clause which has its positive literal as the head.
---------------------------------------------------------------------------------------------------------------*/
% Find the negative literal.
traceBackNeg([P| Args], {{Goals, Ances}, ClInput, Souc}, (LitOrigNeg, (ClauseOrig, SoucOrig))):-
    nth1(I, Goals, -[P|Args1]),
    length(ClInput, L),         % Input clause introduces L-1 subgoals which are placed in front in Goals.
    L > I,
    reform2([[P| Args] = [P|Args1]], [], _, success, success, []), !,   % If this subgoal revolves the targeted one, it is the one where the targeted generated.
    % The newly introduced subgoals includes the targeted subgoal.
    ClauseOrig = ClInput,
    SoucOrig = Souc,
    nth0(I, ClInput, LitOrigNeg).

%Goals does not include the targeted one, trace-back the ancestors: Ances.
traceBackNeg(TgtProp, {{_, Ances}, _, _}, (LitOrigNeg, (ClauseOrig, SoucOrig))):-
    traceBackNeg(TgtProp, Ances, (LitOrigNeg,  (ClauseOrig, SoucOrig))).


traceBackNegbak([P| Args], {{Goals, Ances}, ClInput, Souc}, (LitOrigNeg, (ClauseOrig, SoucOrig))):-
    nth1(I, Goals, -[P|Args1]),
    reform2([[P| Args] = [P|Args1]], [], _, success, success, [])->    % If Goals includes the targeted one:
          (length(ClInput, L),         % Input clause introduces L-1 subgoals which are placed in front in Goals.
           L > I ->
            % The newly introduced subgoals includes the targeted subgoal.
            ClauseOrig = ClInput,
            SoucOrig = Souc,
            nth0(I, ClInput, LitOrigNeg), !;

            % The targeted subgoal is an inherent subgoal from the previous resolutions.
            Ances = {{[-[P2|A21]|_],_}, _, _},
            ClInput = ([+[P2|A2] | _]),
            % Get the substitution of unifying the goal -[P2|A1].
            reform([P2|A21], [P2|A2], [], Substitution, success, success, []),
            % Revert the substitution on GoalTarg.
            subst(Substitution, [P| Args1], TgtPropNew),
            traceBackNeg(TgtPropNew, Ances, (LitOrigNeg,  (ClauseOrig, SoucOrig))));
      %Goals does not include the targeted one, trace-back the ancestors: Ances.
      traceBackNegbak([P| Args], Ances, (LitOrigNeg,  (ClauseOrig, SoucOrig))).

/*********************************************************************************************************************************
    rulesInProof(Proof, RulesIn, AllRules): Find all rules which are involved in the proof
           Find the original rule clauses in the input proof.
    Input: Proof is a proof whose format is (Goals, Ancestors1, InpClause),
           RulesIn is the input rules.
    Output: AllRules are the list of rules which occur in Proof.
**********************************************************************************************************************************/
rulesInProof((_, (_, Source), (ClInput, Souc)), RulesIn, RulesOut):-
    member(Source, [trueSet, falseSet, preferStruc]), !,   % The first resolution step, which is the last to trace back.
    length(ClInput, L),
    (L > 1, \+member((ClInput, Souc), RulesIn) ->               % If it is a newly found rule,
     RulesOut = [(ClInput, Souc)| RulesIn];                     % record it.
     RulesOut = RulesIn).                                       % It is not a rule, terminate.


% Check the ancestor of the proof.
rulesInProof((_, Ancestors, (ClInput, Souc)), RulesIn, RulesOut):-
    length(ClInput, L),
    (L > 1, \+member((ClInput, Souc), RulesIn) ->               % It is a newly found rule.
              RulesTem = [(ClInput, Souc)| RulesIn];            % Record it.
              RulesTem = RulesIn),                              % It is not a rule, terminate.
    rulesInProof(Ancestors, RulesTem, RulesOut).                % Continue to track back the ancestor.

/*********************************************************************************************************************************
    mismatch(Goal, Theory, MPIn, MatchPairs): find the minimal mismatches w.r.t. constants between Gs and the input theory.
    Input:  Goal: a list of sub-goals, [-Subgoal1, -Subgoal2, ...].
            Theory: input theory.
            MPIn: the temporary record of current matched pairs.
    Output: MatchPairs: a list of matched pairs of constants between the Goal and the theory.
            * Match means if replace the constant in the goal by its paired partner, the goal will be resolvable.
**********************************************************************************************************************************/
mismatch([], _, MatchPairs, MatchPairs):-!.
mismatch([-SubGoal| RestGs], Theory, MPIn, MPOut):-
    SubGoal = [Predicate| ArgsG],
    ArgsG = [ExCode| FakeSetups],
    % There should be only one setup in a game.
    member((Clause1, _), Theory),                                        % Get one clause from the theory.
    Clause1 = [+[Predicate| [ExCode| Setups]]| []],                      % Currently, only pair a clause of axiom which has the same predicate with the goal.
    % Get all mismatched arguments of this axiom and the goal.
    % Notice that they should be all constants.
    unpair(FakeSetups, Setups, [], Pairs),

    append(Pairs, MPIn, MP1),
    mismatch(RestGs, Theory, MP1, MPOut).


% Backup code: mismatchBack will find all mismatched constants,including ExCode mismatches.
mismatchBack([], _, MatchPairs, MatchPairs):-!.
mismatchBack([-SubGoal| RestGs], Theory, MPIn, MPOut):-
    SubGoal = [Predicate| ArgsG],
    % There could be several facts of Predicate with different constants. Find them all and get the pairs of unequal arguments of each of them with the goal.
    findall( ConsMismatch,
              (member((Clause1, _), Theory),                                        % Get one clause from the theory.
               Clause1 = [+[Predicate| ArgsH]| Body],
               % Subgoals from the body are resovable --- TODO: need to consider the instantiation from the head.
               % setof(Proof, (slRL((Body, _), TheoryIn, Proof, _), Proof\=[]), _),
               % Currently, only consider use a clause of axiom to match a goal.
               Body == [],
               % Get all unpaired arguments of this axiom and the goal.
               unpair(ArgsG, ArgsH, [], Pairs),
               % Only the unequal pair of constants matter.
               findall(([C1], [C2]),member(([C1], [C2]), Pairs), ConsMismatch)),     % Get the unpaired constants.
             CMismatches),

    % Rank all the pairs and the list with minimal number of unequal constants will be the head of sorted list.
    sort(CMismatches, [MinUnPairs|_]),

    append(MinUnPairs, MPIn, MP1),
    mismatch(RestGs, Theory, MP1, MPOut).


/*********************************************************************************************************************************
    instRule(SufGoals, Rule, InstancesIn, InstancesOut):
            find all instantiations of the Rule.
    Input:  SufGoals: all provable goals with their proofs, [(G1, Proof1), (G2, Proof2),...]. A proof's format is (Goals, Ances, (ClInput, Souc)).
            Rule: the targeted rule.
            InstancesIn: the known instantiations of the Rule.
    Output: InstancesOut: all of the instantiations of the Rule in all proofs.
**********************************************************************************************************************************/
instRule([], _, Ins, Ins):- !.
instRule([(_, Proofs)| Rest], Rule, InstancesIn, InstancesOut):-
    % Get a list of all instantiated body of the rule in wanted proofs.
    setof(Inses, (member(P, Proofs), ruleInProof(P, Rule, [], Inses)), Instances),
    append(Instances, InstancesIn, InstancesNew),
    instRule(Rest, Rule, InstancesNew, InstancesOut).

/*********************************************************************************************************************************
    ruleInProof(Proof, Rule, InstancesIn, InstancesOut):
            find all instantiations of the Rule in a Proof.
    Input:  Proof: a proof's format is (Goals, Ances, (ClInput, Souc)).
            Rule: the targeted rule.
            InstancesIn: the known instantiations of the Rule.
    Output: InstancesOut: a list of all the instantiations of the Rule in the proof.
            *Because a rule can be involved in a proof multiple times, so the length of InstancesOut is the number of that involving times.
**********************************************************************************************************************************/
ruleInProof((_, Source), _, InsList, InsList):-
    member(Source, [trueSet, falseSet, preferStruc]), !,nl,write_term('---------InsList is------'), write_term(InsList),
    InsList\=[].   % The first resolution step, which is the last to trace back.

ruleInProof(Proof, Rule, InsIn, InsOut):-
    Proof = (Goals, Ances, (Clause, _)),
    % Get the instantiated goal from the ancestor, which could be a sequence of resolutions or the initial proposition from the preferred structure.
    % This goal is resolved by the head of Rule.
    (Ances = ([-Goal|_], _, _);
     Ances = ([-Goal],Source),
     member(Source, [trueSet, falseSet, preferStruc])),
    % Get the instantiated rule and record it.
    (Rule = Clause ->
        length(Rule, L), M is L-1,
        length(Body, M), append(Body, _, Goals),          % Get the instantiated body of the rule.
        InsTem= [[+Goal| Body]|InsIn];             % Get the instantiated rule by adding up its instantiated head and body.
        InsTem = InsIn),
    % Continue to find other instantiations of the rule in this proof.
    ruleInProof(Ances, Rule, InsTem, InsOut).


/*********************************************************************************************************************************
    similarity(SufGoals, Goal, Elements, RankIn, Targets).
    Input:  SufGoals: all provable goals with their proofs.
            Goal: a unprovable goal.
            Elements: the elements of Goal in its environment.
            RankIn: the rank of friend goals.
    Output: Targets: a list of provable goals which share same environment elements with Goal.
**********************************************************************************************************************************/
similarity([], _, _, Targets, Rank):- !, sort(Targets, Rank).
similarity([([-G1], Proofs1)| Rest], Goal, EleG, Targets, Rank):-
    environment(X),
    contradiction(Contr),
    member(([G1], Ele1), X),
    setof(Sim, (member(Sim, Ele1), member(Sim, EleG)), Similarities),
    length(Similarities, Num),
    setof((Dif,DifG),
          ( member(Dif, Ele1),
            (member((Dif, DifG), Contr);member((DifG, Dif), Contr)),   % Or axiom(-Dif & -DifG)
            member(DifG, EleG)),
          Differences),
    NewFriend = (Num, [([-G1], Proofs1), Similarities, Differences]),
    similarity(Rest, Goal, Elements, [NewFriend|Targets], Rank).


/*********************************************************************************************************************************
    simRule(AllRules, Similarities, Rule).
    Input:  AllRules: all rule clauses.
            Similarities: similar elements in the given environment.
    Output: Rule is a rule whose body contains the most similarities.
**********************************************************************************************************************************/
simRule([], _, []):- !.
simRule(AllRules, Similarities, BestRule):-
    findall((Score, Rule),
            ( member(Rule, AllRules),
              setof(Sim,
                    ( member([P| Args1], Similarities),
                      member(-[P| Args2], Rule),
                      reform([P| Args1],[P| Args2],[],_,success,success,[]),       % Is a successful resolution.
                      Sim = [P| Args1]),
                    Sims),
               length(Sims, Score)),                % Score is the number of similarities that rule's body covers.
            ScoredRules),
    sort(ScoredRules, RankedScoreRs),
    last(RankedScoreRs, BestRule).

/*********************************************************************************************************************************
    allTheorems(Theory, Constant, Theorems): get all theorems whose arguments include the targeted constant.
    Input:  Theory: the input theory.
            Constant: the targeted constant.
    Output: Theorems is a list of theorem whose argument contains the constant.
**********************************************************************************************************************************/
allTheorems([], _, []):- !.
allTheorems(Theory, Constant, Theorems):-
    % find all therems that can be derived starting with the targeted costant.
    findall(Theorem, 
                (% Get an assertion, +[P| Arugs], from the input theory.
                 member(([+[P| Args]], _), Theory), 
                 member(Constant, Args),
                 % Get a rule from the input theory.
                 member((Clause, Source), Theory),
                 % Not a proposition from the preferred structure.
                 \+member(Source, [falseSet, trueSet]),
                 member(-[P| Arg2], Clause),
                 % The assertion can potentially resolve a precondition of the rule.
                 reform([P| Args], [P| Arg2], [], Substitution, success, success, []),        % If successful resolution
                 delete(Clause, -[P| Arg2], Body),                             % Get the resulting clause C with newly introduced literals Body in front.
                    subst(Substitution, Body, BodyTem),
                    slRL((BodyTem, theorem), Theory, _, [], (_, Theorem, _)),
                 % Check that the targeted constant occur in the arguments of the theorems.
                 Theorem = [+[_| Cons]],
                    member(Constant, Cons)),
                TheoTem1),
        % get all theorems that can be derived by a rule whose head has the targeted constant.
        findall(Theorem, 
                (% Get a rule from the input theory.
                 member((Clause, S), Theory),
                 % Not a proposition from the preferred structure.
                 \+member(S, [falseSet, trueSet]),
                 member(+[_| Arg], Clause),
                 member(Constant, Arg),
                 % Get all theorems that can be derived from this rule.
                    slRL((Clause, S), Theory, _, [], (_, Theorem, _)),
                    % Check that the targeted constant occur in the arguments of the theorems.
                    Theorem = [+[_| Cons]],
                    member(Constant, Cons)),
                TheoTem2),
    append(TheoTem1, TheoTem2, TheoTem), 
    % remove duplicates
    sort(TheoTem, Theorems).
    
/*********************************************************************************************************************************
    general(ClauseIn, ClauseOut): Generalise the axiom by replace the constant which occur more than once with a variable.
    Input:  ClauseIn: the clause to be generalised.
    Output: ClauseOut: the gneralised Clause which has no constant that occurs more than once.
**********************************************************************************************************************************/
generalise([], []):- !.
generalise(ClauseIn, ClauseOut):-
    % get the list of link constants which occur both in the head and the body.
    findall(Constant,
            (member(+[_| ArgHead], ClauseIn),
             member(Constant, ArgHead),
             member(-[_| ArgBody], ClauseIn),
             member(Constant, ArgBody)),
            Cons1),
    % get the list of constants which occur at least twice in the body.
    findall(Constant,
            (member(-[P1| ArgB1], ClauseIn),
             member(-[P2| ArgB2], ClauseIn),
             [P1| ArgB1] \= [P2| ArgB2],
             member(Constant, ArgB1),
             member(Constant, ArgB2)),
            Cons2),
    % get the list of variables in the input clause.
    findall(X,
            ((member(+[P1| ArgB1], ClauseIn),
              member(vble(X), ArgB1));
             (member(-[P2| ArgB2], ClauseIn),
              member(vble(X), ArgB2))),
            VbleList),
    % combine all constant candidates and remove the duplicates by sort them.
    append(Cons1, Cons2, Cons),
    sort(Cons, ConsList),
    getNewVble(ConsList, VbleList, NewVbleSub),
    subst(NewVbleSub, ClauseIn, ClauseOut).
    
% Get substitutions of a new variable for each constant in ConsList and the new variable should not occur in the VL.    
getNewVble(ConsList, VL, NewVbleSub):-
    char_code(z, Zcode),
    getNewVble(ConsList, VL, Zcode, NewVbleSub).
getNewVble([], _, _, []):-!.
% Get one valid new variable with ascii code : Code.
getNewVble([C| CRest], VL, Code, [vble(Char)/C| RestVbleSub]):-
    char_code(Char, Code),
    \+ member(Char, VL),        % the new variable is Char iff it is not one of the list of variables.
    NextCode is Code - 1, !,
    getNewVble(CRest, VL, NextCode, RestVbleSub).
% If the char of Code is already in the variable list, then try the one before it on ascii table.
getNewVble(ConsList, VL, Code, NewVbleSub):-
    NewCode is Code -1,
    getNewVble(ConsList, VL, NewCode, NewVbleSub).
    
    
    
    
    
    
    
    
