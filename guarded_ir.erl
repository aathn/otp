%% Dummy playground for testing whether optimization and extraction can work
%% on guarded IR, as described in the PDF shared in the group chat a while
%% back.
%%
%% In particular this is only meant to explore cost functions, incremental
%% solving, and extraction. The rewriting engine is left out as that's well-
%% trod ground.
%%
%%    -module(q).
%%    -export([q/2]).
%%    
%%    q([A, B], [A]) ->
%%        case A of
%%            0 -> B;
%%            1 -> A
%%        end.
%%
%% erlc guarded_ir.erl && \
%%     ERL_FLAGS="-pa `pwd`" erlc '+{parse_transform,guarded_ir}' q.erl
%%
%%    -module(t).
%%    -export([t/1]).
%%    
%%    t([A]) -> A.
%%
%% erlc guarded_ir.erl && \
%%     ERL_FLAGS="-pa `pwd`" erlc '+{parse_transform,guarded_ir}' t.erl
%%

%%
%% https://www.sciencedirect.com/science/article/pii/S0167642318301187?via%3Dihub
%%
%% The prototype is dead simple at the moment, compiling to our graph form and
%% then extracting a SMT-LIB-like expression from it. There is no reasoning
%% whatsoever at this point.
%%

-module(guarded_ir).
-export([parse_transform/2]).

-type term_id() :: non_neg_integer().

-import(lists, [all/2, any/2, foldl/3, mapfoldl/3,  reverse/1, reverse/2]).

parse_transform(Forms, _Options) ->
    ast(Forms),
    Forms.

%%%%%

%%
%% Rudimentary translation from AST, covering a _very_ small subset of Erlang.
%%

ast([{function, _, _, _, _Clauses}=F | Rest]) ->
    function(F),
    ast(Rest);
ast([_ | Rest]) ->
    ast(Rest);
ast([]) ->
    ok.

function({function, Location, Name, Arity, Clauses0}=F) ->
    Args = [{argument, [{'Int', I}]} || I <- lists:seq(1, Arity)],
    {ArgIds, St0} = mapfoldl(fun eg_term/2, eg_new(), Args),

    {Clauses, St1} =
        clauses(Clauses0, ArgIds, function_clause, St0),

    {Root, St2} = eg_term({function,
                          [{'Location', Location},
                           {'Atom', Name},
                           {'Int', Arity} |
                           [ClauseId || {ClauseId, _Conds} <- Clauses]]},
                          St1),

    St = foldl(fun({Clause, Conds}, Acc) ->
                       eg_equal(Root, Clause, Conds, Acc)
               end, St2, Clauses),

    io:format("# Graph: ~w~n", [St]),
    io:format("# Root: ~w~n", [Root]),

    Kb = kb_build(St),
    io:format("# Knowledge base: ~p~n", [Kb]),

    %%io:format("~w~n", [equivalences(Root, St, Kb, [])]),

    ok.

clauses(Clauses, ArgIds, Class, St) ->
    clauses(Clauses, ArgIds, Class, St, [], []).

%% Clauses must be handled in order. Thus, the later clauses explicitly negate
%% the conditions of the former to prevent overlap.
clauses([Clause | Clauses], ArgIds, Class, St0, OtherGuardIds, Acc) ->
    {ClauseId, GuardIds, ExprId, St1} = clause(Clause, ArgIds, St0),
    {_, NotOthersId, St2} = eg_disjunction(OtherGuardIds, St1),
    St = eg_equal(ClauseId, ExprId, [NotOthersId | GuardIds], St2),
    clauses(Clauses, ArgIds, Class, St,
            GuardIds ++ OtherGuardIds, [{ClauseId, NotOthersId} | Acc]);
clauses([], ArgIds, Class, St0, [_|_]=GuardIds, [_|_]=Acc) ->
    {ExprId, St1} = eg_term({Class, ArgIds}, St0),
    {_, NotOthersId, St} = eg_disjunction(GuardIds, St1),
    {reverse(Acc, [{ExprId, NotOthersId}]), St}.

clause({clause, Location, Patterns, _Guards, [Expr]}, ArgIds, St0) ->
    %% Ignore _Guards for now!
    {PatternIds, GuardIds, St1} = patterns(Patterns, ArgIds, St0),
    {ExprId, St2} = expr(Expr, St1),

    {ASTId, St} = eg_term({clause,
                            [{'Location', Location},
                             ExprId | PatternIds]},
                          St2),

    {ASTId, GuardIds, ExprId, St}.

patterns(Patterns, Ids, St) ->
    patterns_1(Patterns, Ids, [], St).

patterns_1([Pattern | Patterns], [Id | Ids], PreReqs, St0) ->
    {PatternIds, GuardIds0, St1} = patterns_1(Patterns, Ids, PreReqs, St0),
    {PatternId, GuardIds, St} = pattern(Pattern, Id, PreReqs, St1),
    {[PatternId | PatternIds], GuardIds ++ GuardIds0, St};
patterns_1([], [], _PreReqs, St) ->
    {[], [], St}.

expr({'case', Location, Expr, Cs}, St0) ->
    {ExprId, St1} = expr(Expr, St0),
    {Clauses, St2} = clauses(Cs, [ExprId], case_clause, St1),

    {CaseId, St3} =
        eg_term({'case',
                 [{'Location', Location},
                  ExprId | [ClauseId || {ClauseId, _Conds} <- Clauses]]},
                 St2),

    St = foldl(fun({Clause, Conds}, Acc) ->
                       eg_equal(CaseId, Clause, Conds, Acc)
               end, St3, Clauses),

    {CaseId, St};
expr({var, Location, V}, St0) ->
    {ASTId, St1} = eg_term({var, [{'Location', Location}, {'Atom', V}]}, St0),
    {LoweredId, St} = eg_term({variable, [{'Atom', V}]}, St1),

    {ASTId, eg_equal(ASTId, LoweredId, [], St)}.

pattern({var, Location, V}, Id, PreReqs, St0) ->
    {ASTId, St1} = eg_term({var, [{'Location', Location}, {'Atom', V}]}, St0),

    {LoweredId, St2} = eg_term({variable, [{'Atom', V}]}, St1),
    St3 = eg_equal(ASTId, LoweredId, [], St2),

    {GuardId, _, St} = eg_condition({same, [Id, LoweredId]}, PreReqs, St3),
    {ASTId, [GuardId], eg_equal(Id, ASTId, [GuardId | PreReqs], St)};
pattern({integer, Location, I}, Id, PreReqs, St0) ->
    {ASTId, St1} = eg_term({integer,
                            [{'Location', Location}, {'Int', I}]},
                           St0),

    {LoweredId, St2} = eg_term({integer_term, [{'Int', I}]}, St1),
    St3 = eg_equal(ASTId, LoweredId, [], St2),
    {GuardId, _, St} = eg_condition({same, [Id, LoweredId]}, PreReqs, St3),

    {ASTId, [GuardId], eg_equal(LoweredId, Id, [GuardId | PreReqs], St)};
pattern({atom, Location, A}, Id, PreReqs, St0) ->
    {ASTId, St1} = eg_term({atom, [{'Location', Location}, {'Atom', A}]}, St0),

    {LoweredId, St2} = eg_term({atom_term, [{'Atom', A}]}, St1),
    St3 = eg_equal(ASTId, LoweredId, [], St2),
    {GuardId, _, St} = eg_condition({same, [Id, LoweredId]}, PreReqs, St3),

    {ASTId, [GuardId], eg_equal(LoweredId, Id, [GuardId | PreReqs], St)};
pattern({nil, Location}, Id, PreReqs, St0) ->
    {ASTId, St1} = eg_term({nil, [{'Location', Location}]}, St0),

    {LoweredId, St2} = eg_term({nil_term, []}, St1),
    St3 = eg_equal(ASTId, LoweredId, [], St2),
    {GuardId, _, St} = eg_condition({same, [Id, LoweredId]}, PreReqs, St3),

    {ASTId, [GuardId], eg_equal(LoweredId, Id, [GuardId | PreReqs], St)};
pattern({cons, Location, H, T}, Id, PreReqs, St0) ->
    {GuardId, _, St1} = eg_condition({{is, cons}, [Id]}, PreReqs, St0),

    {H_Lowered_Id, St2} = eg_subterm({head_value, [Id]}, Id, St1),
    {T_Lowered_Id, St3} = eg_subterm({tail_value, [Id]}, Id, St2),
    {Cons_Lowered_Id, St4} =
        eg_term({cons_term, [H_Lowered_Id, T_Lowered_Id]}, St3),

    {H_AST_Id, Gs0, St5} = pattern(H, H_Lowered_Id, [GuardId | PreReqs], St4),
    {T_AST_Id, Gs1, St6} = pattern(T, T_Lowered_Id, [GuardId | PreReqs], St5),
    {Cons_AST_Id, St7} = eg_term({cons,
                                  [{'Location', Location},
                                   H_AST_Id,
                                   T_AST_Id]},
                                 St6),

    St = eg_equal(Cons_AST_Id, Cons_Lowered_Id, [GuardId | PreReqs], St7),

    {Cons_AST_Id, Gs0 ++ Gs1, St}.

%%%%%

-record(eg, { counter = 0 :: term_id(),
              bindings = #{},
              expressions = #{},
              equalities = #{} ::
                #{ term_id() => ordsets:ordset({term_id(), [term_id()]}) },
              singletons = gb_sets:new() :: gb_sets:set(),
              subterms = #{} :: #{ term_id() => ordsets:ordset(term_id()) } }).

-record(term, {op, args}).

eg_new() ->
    #eg{}.

%% Binds `Expr` as a term equal only to itself, usually this is called "atom"
%% in literature but we don't want this to be confused with Erlang atoms.
eg_singleton(Expr, Eg0) ->
    {Id, #eg{singletons=Gs0}=Eg} = eg_bind(Expr, Eg0),
    {Id, Eg#eg{singletons=gb_sets:add(Id, Gs0)}}.

eg_bind(Expr, #eg{bindings=Bs}=Eg0) ->
    case Bs of
        #{ Expr := Id } ->
            {Id, Eg0};
        #{} ->
            {Id, Eg} = eg_new_id(Eg0),
            eg_assign(Id, Expr, Eg)
    end.

eg_assign(Id, Expr, #eg{bindings=Bs0,expressions=Exprs0}=Eg) ->
    false = is_map_key(Expr, Bs0) orelse is_map_key(Id, Exprs0), %Assertion.
    Bs = Bs0#{ Expr => Id },
    Exprs = Exprs0#{ Id => Expr },
    {Id, Eg#eg{bindings=Bs,expressions=Exprs}}.

eg_new_id(#eg{counter=Counter0}=Eg) ->
    Counter = Counter0 + 1,
    {Counter0, Eg#eg{counter=Counter}}.

eg_phi(Eg0) ->
    {Id, Eg} = eg_new_id(Eg0),
    eg_assign(Id, {phi, Id}, Eg).

eg_equal(Same, Same, _Conds, Eg0) when is_integer(Same) ->
    Eg0;
eg_equal(LHS_Id, RHS_Id, Conds, Eg) when is_integer(LHS_Id),
                                         is_integer(RHS_Id) ->
    %% FIXME: If we already have an edge between LHS and RHS, should we join
    %% the conditions with a phi instead of adding another edge altogether?
    %%
    %% This might simplify contraction a bit.
    #eg{equalities=Eqs0} = Eg,

    LHS_Eq = maps:get(LHS_Id, Eqs0, ordsets:new()),
    RHS_Eq = maps:get(RHS_Id, Eqs0, ordsets:new()),

    Eqs = Eqs0#{ LHS_Id => ordsets:add_element({RHS_Id, Conds}, LHS_Eq),
                 RHS_Id => ordsets:add_element({LHS_Id, Conds}, RHS_Eq) },

    Eg#eg{equalities=Eqs};
eg_equal(LHS, RHS, Conds, Eg0) ->
    {LHS_Id, Eg1} = eg_term(LHS, Eg0),
    {RHS_Id, Eg} = eg_term(RHS, Eg1),
    eg_equal(LHS_Id, RHS_Id, Conds, Eg).

eg_subterm(Expr, SuperId, Eg0) ->
    {Id, #eg{subterms=Subterms0}=Eg} = eg_term(Expr, Eg0),

    Others = maps:get(SuperId, Subterms0, ordsets:new()),
    Subterms = Subterms0#{ SuperId => ordsets:add_element(Id, Others) },

    {Id, Eg#eg{subterms=Subterms}}.

eg_term(Id, Eg0) when is_integer(Id) ->
    {Id, Eg0};
eg_term({Location, _}=Expr, Eg0)
  when Location =:= 'Atom';
       Location =:= 'Bool';
       Location =:= 'Int';
       Location =:= 'Location' ->
    eg_singleton(Expr, Eg0);
eg_term({Op, Args}, Eg0) when is_list(Args) ->
    {ArgIds, Eg} = mapfoldl(fun eg_term/2, Eg0, Args),
    eg_bind(#term{op=Op,args=ArgIds}, Eg).

%% Conditions are a special beast in this representation. While they are terms
%% like any other, we must be able to enforce an order on conditions so that we
%% can test certain things before others, for example that a term is a tuple
%% before we try to test whether the first element is the expected record tag.
%%
%% To achieve this, we (conceptually) walk backwards from 'true' toward the
%% target conditions when evaluating them, effectively creating an ordered
%% conjunction.
%%
%% This distinction is only meaningful during code generation, and we can
%% ignore it entirely during the reasoning phase. As long as we don't link
%% the protected condition to 'true' without first having made sure that the
%% prerequisites hold, we should be fine.
eg_condition(Expr, [], St0) ->
    {ExprId, St} = eg_term(Expr, St0),
    eg_boolean(ExprId, St);
eg_condition(Expr, PreReqs, St0) ->
    %% Create a (boolean) phi to split the expression from the PreReqs, this is
    %% ugly but necessary as `Expr` is wholly invalid without them, and thus we
    %% cannot link directly to 'true' and 'false'.
    {PhiId, St1} = eg_phi(St0),

    {PosId, NegId, St2} = eg_boolean(PhiId, St1),

    %% The phi is false when any of the prerequisites are unmet.
    NegPreReqs = eg_negate(PreReqs, St2),
    {PreReqsUnmet, _PreReqsMet, St3} = eg_disjunction(NegPreReqs, St2),
    St5 = eg_equal(PosId, {'Bool', false}, [PreReqsUnmet], St3),

    %% The phi is equal to the tested expression iff the prerequisies are all
    %% met.
    {BoolId, St6} = eg_term(Expr, St5),
    St = eg_equal(BoolId, PosId, PreReqs, St6),

    {PosId, NegId, St}.

%% We can only negate booleans, all of which should already have a negation
%% present in the graph. Hence, we do not update the state.
eg_negate([Cond | Conds0], St) ->
    Conds = eg_negate(Conds0, St),
    {NegId, St} = eg_term({'not', [Cond]}, St), %Assertion.
    [NegId | Conds];
eg_negate([], _St) ->
    [].

eg_disjunction(Conditions, St0) ->
    {PhiId, St1} = eg_phi(St0),
    {PosId, NegId, St2} = eg_boolean(PhiId, St1),
    St = foldl(fun(Cond, Acc0) ->
                       Acc = eg_equal(PosId, {'Bool', true}, [Cond], Acc0),
                       eg_equal(Cond, {'Bool', false}, [NegId], Acc)
               end, St2, Conditions),
    {PhiId, NegId, St}.

eg_boolean(BoolId, St0) ->
    %% A negation must exist for all booleans, including the negation itself.
    %%
    %% For brevity, we will not return the negation of the negation, and merely
    %% mark it as unconditionally equal to the expression.
    {NegId, St1} = eg_term({'not', [BoolId]}, St0),
    {PosId, St2} = eg_term({'not', [NegId]}, St1),
    St3 = eg_equal(PosId, BoolId, [], St2),

    St4 = eg_equal(BoolId, {'Bool', true}, [BoolId], St3),
    St5 = eg_equal(NegId, {'Bool', false}, [BoolId], St4),
    St6 = eg_equal(NegId, {'Bool', true}, [NegId], St5),
    St = eg_equal(BoolId, {'Bool', false}, [NegId], St6),

    {BoolId, NegId, St}.

%%%%%

%%%
%%% To prevent infinite expansion during equivalence extraction, we must
%%% perform some basic reasoning to determine whether we've already satisfied a
%%% condition or not, directly or indirectly.
%%%
%%% While we could invoke a snazzy external theorem prover, we already have all
%%% the information we need encoded in the graph, as informed by the rewrite
%%% rules.
%%%
%%% As singletons (such as the boolean 'true') equal only themselves, any
%%% equivalence between distinct singletons is impossible, and the combination
%%% of conditions that make them equal must be false.
%%%
%%% In other words, at least one condition on the path between two singletons
%%% must be false, which makes it a Horn formula: solvable in linear time,
%%% and for our purposes "N" is a pretty low number.
%%%
%%% By finding all paths between all singletons, we get a set of Horn clauses
%%% representing all known impossibilites and can use them to statically
%%% disprove conditions, or conversely prove conditions by negation.
%%%

-type clause_id() :: non_neg_integer().

-record(kb, { counter = 0 :: clause_id(),
              clauses = #{} :: #{ clause_id() => gb_sets:set(term_id()) },
              usage = #{} :: #{ term_id() => gb_sets:set(clause_id()) } }).

kb_build(Eg) ->
    Kb = kb_derive_from_singletons(Eg, #kb{}),
    kb_derive_from_subterms(Eg, Kb).

%% Generates rejection clauses for conditions that lead to two singletons being
%% equal.
%%
%% Note that this may generate redundant clauses, for example if we have two
%% impossible paths (x ∧ y ⌐x) and (x ∧ ⌐x), then we can get one or both of
%% them depending on the order we check them. This is benign and we don't make
%% any attempts to optimize this.
kb_derive_from_singletons(#eg{singletons=Sgs}=Eg, Kb0) ->
    EdgeFun = fun(_From, {To, _Conds}) ->
                      case gb_sets:is_element(To, Sgs) of
                          true -> reject;
                          false -> continue
                      end
              end,
    {Kb, _} = gb_sets:fold(fun (Id, Acc) ->
                                   kb_build_traverse(EdgeFun, Eg, Acc, Id)
                           end, {Kb0, #{}}, Sgs),
    Kb.

kb_derive_from_subterms(#eg{subterms=_Sgs}=_Eg, Kb0) ->
    %% FIXME: Traverse both the subterm graph _and_ equalities modulo
    %% conditions.
    Kb0.

% kb_derive_from_subterms_1(Eg, Path, {To, _Conds}, {Bs, Kb}=Acc) ->
%     case kb_impossible(Path, Eg, Kb) of
%         true ->
%             {false, Acc};
%         false ->
%             case gb_sets:is_element(To, Eg#eg.singletons) of
%                 true -> {false, kb_contradiction(Path, Bs, Kb)};
%                 false -> {true, Acc}
%             end
%     end.

kb_build_traverse(EdgeFun, Eg, {Kb0, Bs0}, Id) ->
    {_, Kb, Bs} = kbbt_vertex(Id, Id, EdgeFun, Eg, #{}, [], Kb0, Bs0),
    {Kb, Bs}.

kbbt_vertex(Id, Root, EdgeFun, Eg, Paths0, Path, Kb, Bs) ->
    #kb{} = Kb, %Assertion.
    Prev = maps:get(Id, Paths0, []),
    case any(fun(E) -> ordsets:is_subset(E, Path) end, Prev) of
        true ->
            %% We've already visited this node with the same conditions, skip
            %% it.
            {Paths0, Kb, Bs};
        false ->
            Paths = Paths0#{ Id => [Path | Prev] },
            Edges = maps:get(Id, Eg#eg.equalities, []),
            kbbt_edges(Edges, Id, Root, EdgeFun, Eg, Paths, Path, Kb, Bs)
    end.

kbbt_edges([{Root, _} | Edges],
           From, Root, EdgeFun, Eg, Paths, Path, Kb, Bs) ->
    #kb{} = Kb, %Assertion.
    kbbt_edges(Edges, From, Root, EdgeFun, Eg, Paths, Path, Kb, Bs);
kbbt_edges([{To, Conds}=Edge | Edges],
          From, Root, EdgeFun, Eg, Paths0, Path0, Kb0, Bs0) ->
    #kb{} = Kb0, %Assertion.
    true = From =/= To,                         %Assertion.
    Path = ordsets:union(ordsets:from_list(Conds), Path0),
    Decision = case kb_impossible(Path, Eg, Kb0) of
                   true -> skip;
                   false -> EdgeFun(From, Edge)
               end,
    case Decision of
        continue ->
            {Paths, Kb, Bs} =
                kbbt_vertex(To, Root, EdgeFun, Eg, Paths0, Path, Kb0, Bs0),
            kbbt_edges(Edges, From, Root, EdgeFun, Eg, Paths, Path0, Kb, Bs);
        reject ->
            {Kb, Bs} = kb_contradiction(Path, Kb0, Bs0),
            kbbt_edges(Edges, From, Root, EdgeFun, Eg, Paths0, Path0, Kb, Bs);
        skip ->
            kbbt_edges(Edges, From, Root, EdgeFun, Eg, Paths0, Path0, Kb0, Bs0)
    end;
kbbt_edges([], _From, _Root, _EdgeFun, _Eg, Paths, _Path, Kb, Bs) ->
    {Paths, Kb, Bs}.

kb_contradiction(Path, Kb0, Bs0) ->
    #kb{counter=Counter,clauses=Cs,usage=Us0} = Kb0,
    case Bs0 of
        #{ Path := _ } ->
            %% Already exists.
            {Kb0, Bs0};
        #{} ->
            Us = foldl(fun(Id, Acc) ->
                            Prev = maps:get(Id, Acc, gb_sets:empty()),
                            Acc#{ Id => gb_sets:add_element(Counter, Prev) }
                       end, Us0, Path),
            Bs = Bs0#{ Path => Counter },
            Kb = Kb0#kb{counter=Counter + 1,
                        clauses=Cs#{ Counter => gb_sets:from_list(Path) },
                        usage=Us},
            {Kb, Bs}
    end.

%% Naive Horn "unsatisifiability solver," that is only capable of returning
%% whether a set of facts are definitely unsatisfiable. It does not attempt to
%% find an assignment of variables, it merely returns whether an assignment
%% could exist.
%%
%% While expressions aren't actually literals, we can treat them as such
%% because the boolean logic is handled by the graph; any contradiction
%% produced by an expression canceling another out will be handled by another
%% clause.
%%
%% This includes negations. The impossibility of A and (not A) holding at the
%% same time is encoded in the Horn formulas derived from traversing between
%% 'true' and 'false'.
%%
%%    let B = (not A)
%%    true <A- A -B> false
%%    true <B- B -A> false
%%
%% Yielding (⌐A ∨ ⌐B)
kb_impossible(Facts0, Eg, #kb{clauses=Cs,usage=Us}) ->
    Facts = gb_sets:from_list(Facts0),

    %% To force negations to contradict each other without having to make the
    %% solver understand booleans, we have to include all clauses that involve
    %% negations of our provided facts.
    NegatedFacts = gb_sets:from_list(eg_negate(Facts0, Eg)),
    RelatedFacts = gb_sets:union(Facts, NegatedFacts),
    kbi_facts(gb_sets:next(gb_sets:iterator(RelatedFacts)),
              Facts, Cs, Us, gb_sets:new()).

kbi_facts({Id, Iterator}, Facts, Cs, Us, Seen0) ->
    %% Find all the clauses in which `Id` is used and that we haven't seen
    %% before, and check whether they are possible.
    Uses = maps:get(Id, Us, gb_sets:empty()),
    Unseen = gb_sets:subtract(Uses, Seen0),
    case kbi_clauses(gb_sets:next(gb_sets:iterator(Unseen)), Facts, Cs) of
        true ->
            true;
        false ->
            Seen = gb_sets:union(Unseen, Seen0),
            kbi_facts(gb_sets:next(Iterator), Facts, Cs, Us, Seen)
    end;
kbi_facts(none, _Facts, _Cs, _Us, _Seen) ->
    false.

kbi_clauses({ClauseId, Iterator}, Facts, Cs) ->
    %% As all of our clauses are of the form `(⌐x ∨ ⌐y ∨ ...)`, and negations
    %% are facts like any other, we can determine unsatisfiability by checking
    %% whether any clause becomes empty if we remove the known facts.
    #{ ClauseId := Negations } = Cs,
    case gb_sets:is_subset(Negations, Facts) of
        true -> true;
        false -> kbi_clauses(gb_sets:next(Iterator), Facts, Cs)
    end;
kbi_clauses(none, _Facts, _Cs) ->
    false.

%%%%%

%%%
%%% To prevent having to reason about a silly amount of candidates, especially
%%% booleans which are all linked together, extraction is guided by a heuristic
%%% that stops the search once the runtime cost of a candidate (including the
%%% work needed to reach it) exceeds the cost of the best unconditional
%%% candidate.
%%%
%%% We also check for logical contradictions to avoid infinite loops, using the
%%% "knowledge base" structure defined above.
%%%

equivalences(Id, #eg{}=Eg, Kb, Path) ->
    equivalences_1(Id, Eg, Kb, #{}, Path, term_cost(Id, Eg)).

equivalences_1(Id, #eg{expressions=Exprs,equalities=Eqs}=Eg, Kb,
               Acc0, Path0, Ceiling0) ->
    Prev = maps:get(Id, Acc0, []),
    case any(fun(E) -> ordsets:is_subset(E, Path0) end, Prev) of
        true ->
            %% We've already seen this perspective, skip it.
            Acc0;
        false ->
            %% HACK: phis must produce a value. Reset the cost ceiling so we
            %% don't skip their content unless we've already visited it.
            Ceiling = case Exprs of
                          #{ Id := {phi, _} } -> infinity;
                          #{ Id := _ } -> Ceiling0
                      end,
            Acc1 = Acc0#{ Id => [Path0 | Prev] },
            foldl(fun({To, Conds}, Acc) ->
                          Cost = term_cost(To, Eg),
                          Path = ordsets:union(ordsets:from_list(Conds),
                                               Path0),
                          case ((path_cost(Conds, Eg) + Cost) =< Ceiling
                                andalso (not kb_impossible(Path, Eg, Kb))) of
                              true ->
                                  equivalences_1(To, Eg, Kb, Acc, Path, Cost);
                              false ->
                                  Acc
                          end
                  end, Acc1, maps:get(Id, Eqs, []))
    end.

term_cost(Id, #eg{expressions=Exprs}) ->
    case Exprs of
        #{ Id := #term{} } ->
            %% Assume all operations have the same cost for now.
            1;
        #{ Id := _PhiOrLiteral } ->
            %% Phis and literals don't cost anything in and of themselves;
            %% traversal and evaluation costs are accounted for separately.
            0
    end.

path_cost(Path, Eg) ->
    foldl(fun(Id, Acc) -> term_cost(Id, Eg) + Acc end, 0, Path).
