:- use_module(iso_predicates).
:- use_module(prolog_code).
:- use_module(ansi_termx). 
:- use_module(util).

:- dynamic notrace/0.

% main call:
rdebug(G) :- 
   comma_list(G,[A|_]),
   matching_clauses(A,[],[]), !,
   fail.
rdebug(G) :- 
   comma_list(G,[A|T]),
   matching_clauses(A,[],Clauses), !,
   retractall(notrace),
   solve([A|T],[],[],Clauses,0,[A|T]).

%%solving goals (deterministic):

solve(_G,_L,_ClausesDone,_ClausesPending,Del,_InitialGoal) :-
  %format("Del: ~w~n",[Del]),
  delete_subcomputation(Del),
  fail.

%% Reached a successful leaf of the SLD tree:
solve([],L,ClausesDone,ClausesPending,Del,InitialGoal) :-
   print_solution(InitialGoal,L),nl,
   read_keyatom(Key),
   (Key=up ->          !, retractall(notrace),backward_step([],L,0,InitialGoal)
    ; Key=semicolon -> !, retractall(notrace),next_choice([],L,ClausesDone,ClausesPending,1,InitialGoal)
    ; Key=enter ->     !, retractall(notrace),abort
    ; Key=down ->      !, retractall(notrace),abort
    ; Key=left ->      !, retractall(notrace),cursor_move(2,up),solve([],L,ClausesDone,ClausesPending,Del,InitialGoal)
    ; Key=right ->     !, retractall(notrace),cursor_move(2,up),solve([],L,ClausesDone,ClausesPending,Del,InitialGoal)
    ; Key=skip ->      !, retractall(notrace),assert(notrace),next_choice([],L,ClausesDone,ClausesPending,1,InitialGoal)
    ; format("ERROR"), abort
   ).

%% Built-in call (a solution exists):
solve([A|T],L,_,_,_Del,InitialGoal) :-
   iso_builtin_predicate(A),
   copy_term((A,L),(Acopy,Lcopy)),
   unify(Lcopy), 
   call(Acopy),
   !,
   %format("Del: ~w~n",[Del]),
   print_goal([A|T],L),
   append(L,[builtin(A)],NL), 
   print_success([A|T],NL),
   (notrace, !, Key=enter ; read_keyatom(Key)),
   (Key=up ->       !, retractall(notrace),backward_step([A|T],L,0,InitialGoal)
    ; Key=enter ->  !, solve_check(T,NL,0,InitialGoal)
    ; Key=skip ->   !, assertz(notrace), solve_check(T,NL,0,InitialGoal)
    ; Key=down ->   !, solve_check(T,NL,0,InitialGoal)
    ; Key=left ->   !, move_left([A|T],L,[],[],0,InitialGoal)
    ; Key=right ->  !, move_right([A|T],L,[],[],0,InitialGoal)
    ; format("ERROR"), abort
   ).

%% Built-in call (no solution):
solve([A|T],L,_,_,_Del,InitialGoal) :-
   iso_builtin_predicate(A),!,
   %format("Del: ~w~n",[Del]),
   print_goal([A|T],L),
   print_failure([A|T],L),
   retractall(notrace),
   %(notrace, !, Key=enter ; read_keyatom(Key)),
   read_keyatom(Key),
   (Key=up ->      !, retractall(notrace),backward_step([A|T],L,0,InitialGoal)
    ; Key=enter -> !, next_choice([A|T],L,[],[],0,InitialGoal)
    ; Key=down ->  !, next_choice([A|T],L,[],[],0,InitialGoal)
    ; Key=left ->  !, move_left([A|T],L,[],[],0,InitialGoal)
    ; Key=right -> !, move_right([A|T],L,[],[],0,InitialGoal)
    ; Key=skip ->  !, retractall(notrace),assert(notrace),next_choice([A|T],L,[],[],0,InitialGoal)
    ; format("ERROR"), abort
   ).

%% User-defined call (no more matching clauses, do not print fail):
solve(G,L,ClausesDone,[],_Del,InitialGoal) :-
   !,
   %NDepth is Depth-1,
   %delete_subcomputation(1),
   next_choice(G,L,ClausesDone,[],0,InitialGoal).

%% User-defined call (some matching clauses remaining):
solve([A|T],L,ClausesDone,[Ref|ClausesPending],_Del,InitialGoal) :-
   append(ClausesDone,[Ref|ClausesPending],Foo),length(Foo,FooN),
   (FooN>1,!,print_goal_nondet([A|T],L) ; print_goal([A|T],L)),
   %delete_subcomputation(NN),
   clause(H,B,Ref),
   comma_list(B,Blist),
   add_to_list(Blist,T,NT),
   size(Blist,Blen),
   append(ClausesDone,[Ref],NewClausesDone),
   append(L,[user(A,H,Blen,NewClausesDone,ClausesPending)],NL),
   print_success([A|T],NL),
   (notrace, !, Key=enter ; read_keyatom(Key)),
   (Key=up ->       !, retractall(notrace),backward_step([A|T],L,0,InitialGoal)
    ; Key=enter ->  !, solve_check(NT,NL,0,InitialGoal)
    ; Key=skip ->   !, assertz(notrace), solve_check(NT,NL,0,InitialGoal)
    ; Key=down ->   !, solve_check(NT,NL,0,InitialGoal)
    ; Key=left ->   !, move_left([A|T],L,ClausesDone,[Ref|ClausesPending],0,InitialGoal)
    ; Key=right ->  !, move_right([A|T],L,ClausesDone,[Ref|ClausesPending],0,InitialGoal)
    ; format("ERROR"), abort
   ).

move_left(G,L,[],ClausesPending,Del,InitialGoal) :-
  !, 
  delete_subcomputation_simple(1),
  solve(G,L,[],ClausesPending,Del,InitialGoal).
move_left(G,L,ClausesDone,ClausesPending,Del,InitialGoal) :-
  delete_subcomputation_simple(1),
  append(NewClausesDone,[Ref],ClausesDone),
  solve(G,L,NewClausesDone,[Ref|ClausesPending],Del,InitialGoal).

move_right(G,L,[],[],Del,InitialGoal) :-
  delete_subcomputation_simple(1),
  !, solve(G,L,[],[],Del,InitialGoal).
move_right(G,L,ClausesDone,[Ref],Del,InitialGoal) :-
  delete_subcomputation_simple(1),
  !, solve(G,L,ClausesDone,[Ref],Del,InitialGoal).
move_right(G,L,ClausesDone,[Ref|ClausesPending],Del,InitialGoal) :-
  delete_subcomputation_simple(1),
  append(ClausesDone,[Ref],NewClausesDone),
  solve(G,L,NewClausesDone,ClausesPending,Del,InitialGoal).


%% Adding a new goal: a leaf
solve_check([],NL,Del,InitialGoal) :-
   !, 
   %NDepth is Depth+1,
   solve([],NL,[],[],Del,InitialGoal).

%% Adding a new goal: built in
solve_check([A|T],L,Del,InitialGoal) :-
   iso_builtin_predicate(A),!,
   solve([A|T],L,[],[],Del,InitialGoal).

%% Adding a new goal: no matching clauses
solve_check([A|T],L,Del,InitialGoal) :-
   matching_clauses(A,L,[]), !,  %%failing goal
   %NDepth is Depth+1,
   %format("Del: ~w~n",[Del]),
   print_goal([A|T],L),
   print_failure([A|T],L),
   %NN is 2*(Depth-Last+1), 
   %NLast is Last+1,
   retractall(notrace),
   %(notrace, !, Key=enter ; read_keyatom(Key)),
   read_keyatom(Key),
   (Key=up ->      !, retractall(notrace),backward_step([A|T],L,Del,InitialGoal)
    ; Key=enter -> !, next_choice([A|T],L,[],[],Del,InitialGoal)
    ; Key=down ->  !, next_choice([A|T],L,[],[],Del,InitialGoal)
    ; Key=left ->  !, delete_subcomputation_simple(1),solve_check([A|T],L,Del,InitialGoal)
    ; Key=right -> !, delete_subcomputation_simple(1),solve_check([A|T],L,Del,InitialGoal)
    ; Key=skip ->  !, retractall(notrace),assert(notrace),next_choice([A|T],L,[],[],Del,InitialGoal)
    ; format("ERROR"), abort
   ).

%% Adding a new goal: a non-empty set of matching clauses
solve_check([A|T],L,Del,InitialGoal) :-
   matching_clauses(A,L,Clauses), !,  %%sucess
   %NDepth is Depth+1,
   %length(Clauses,Num),
   %(Num>1, !, NNDList = [NDepth|NDList]; NNDList=NDList),
   solve([A|T],L,[],Clauses,Del,InitialGoal).

delete_subcomputation_simple(N) :-
   M is N+1,
   cursor_move(M,up),
   delete_subcomputation_aux(M,M).

delete_subcomputation(0) :- !.
delete_subcomputation(N) :-
   M is 2*(N+1),
   cursor_move(M,up),
   delete_subcomputation_aux(M,M).

delete_subcomputation_aux(0,N) :- !, cursor_move(N,up).
delete_subcomputation_aux(N,M) :-
   format("                                                                                ~n"),
   NN is N-1, delete_subcomputation_aux(NN,M).

is_pending_choice([user(_,_,_,_,[_|_])|_]) :- !.
is_pending_choice([user(_,_,_,_,[])|R]) :- !, is_pending_choice(R).
is_pending_choice([builtin(_)|R]) :- !, is_pending_choice(R).

%%%
%next_choice(G,[],ClausesDone,[],Del,InitialGoal) :- !, 
%   read_keyatom(Key),
%   (Key=up ->      !, retractall(notrace),backward_step(G,[],Del,InitialGoal)
%    ; Key=enter -> !, next_choice(G,[],ClausesDone,[],Del,InitialGoal)
%    ; Key=down ->  !, next_choice(G,[],ClausesDone,[],Del,InitialGoal)
%    ; Key=left ->  !, next_choice(G,[],ClausesDone,[],Del,InitialGoal)
%    ; Key=right -> !, next_choice(G,[],ClausesDone,[],Del,InitialGoal)
%    ; format("ERROR"), abort
%   ).
next_choice(G,L,_Done,[],Del,InitialGoal) :- 
   not(is_pending_choice(L)),
   !,
   format("No more solutions...~n"),
   read_keyatom(Key),
   (Key=up -> !, cursor_move(1,up),
                 format("                                                                                ~n"),
   	             cursor_move(1,up),
   	             retractall(notrace),backward_step(G,L,Del,InitialGoal)
    ; abort
   ).
next_choice([],L,_,[],Del,InitialGoal) :- 
   append(NL, [user(A,_,_,ClausesDone,ClausesPending)], L), 
   %remove_elements(Len,G,NG),!,
   %NN is OldDepth - Depth,
   %NDel is Del+1,
   %delete_subcomputation(1),
   %NDepth is Depth-1,
   next_choice([A],NL,ClausesDone,ClausesPending,Del,InitialGoal).
next_choice([],L,_,[],Del,InitialGoal) :- 
   append(NL, [builtin(A)], L), !,
   %NN is OldDepth - Depth,
   %NDel is Del+1,
   %delete_subcomputation(1),
   %NDepth is Depth-1,
   next_choice([A],NL,[],[],Del,InitialGoal).
next_choice(G,L,_,[],Del,InitialGoal) :- 
   append(NL, [user(A,_,Len,ClausesDone,ClausesPending)], L), 
   remove_elements(Len,G,NG),!,
   %NN is OldDepth - Depth,
   NDel is Del+1,
   %delete_subcomputation(1),
   %NDepth is Depth-1,
   next_choice([A|NG],NL,ClausesDone,ClausesPending,NDel,InitialGoal).
next_choice(G,L,_,[],Del,InitialGoal) :- 
   append(NL, [builtin(A)], L), !,
   %NN is OldDepth - Depth,
   NDel is Del+1,
   %delete_subcomputation(1),
   %NDepth is Depth-1,
   next_choice([A|G],NL,[],[],NDel,InitialGoal).
next_choice(G,L,ClausesDone,ClausesPending,Del,InitialGoal) :-
   %delete_subcomputation_simple(1),
   solve(G,L,ClausesDone,ClausesPending,Del,InitialGoal).


matching_clauses(A,L,Clauses) :- 
   copy_term((A,L),(Acopy,Lcopy)),
   unify(Lcopy),
   findall(Ref,clause(Acopy,_,Ref),Clauses).

%%%

%% this is a special case to avoid undoing the first call:
backward_step([A|T],[],Del,InitialGoal) :-
   matching_clauses(A,[],Clauses), !,
   cursor_move(2,up),
   %NDel is Del+1,
   solve([A|T],[],[],Clauses,Del,InitialGoal).

backward_step(G,L,_Del,InitialGoal) :-
  append(NL, [user(A,_,Len,ClausesDone,ClausesPending)], L), 
  append(NewClausesDone,[Ref],ClausesDone),
  remove_elements(Len,G,NG),!,
  %matching_clauses(A,NL,NClauses),
  %%cursor_move(2,up),
  %%format("                                                                                ~n"),
  %%format("                                                                                ~n"),
  %%cursor_move(4,up),
  %NDepth is Depth-1,
  %NN is OldDepth - Depth,
  %format("~w is ~w - ~w~n",[NN,OldDepth,Depth]),
  delete_subcomputation(1),
  %NDel is Del+1,
  solve([A|NG],NL,NewClausesDone,[Ref|ClausesPending],0,InitialGoal).

backward_step(G,L,_Del,InitialGoal) :-
  append(NL, [builtin(A)], L), !,    %% built-ins are assumed deterministic
  %%cursor_move(2,up),
  %%format("                                                                                ~n"),
  %%format("                                                                                ~n"),
  %%cursor_move(4,up),
  %NDepth is Depth-1,
  %NN is OldDepth - Depth,
  %format("~w is ~w - ~w~n",[NN,OldDepth,Depth]),
  delete_subcomputation(1),
  %NDel is Del+1,
  solve_check([A|G],NL,0,InitialGoal).

remove_elements(0,G,G) :- !.
remove_elements(N,[_|R],G) :- M is N-1, remove_elements(M,R,G).

size([true],0) :- !.
size(L,N) :- length(L,N).

add_to_list([true],T,T) :- !.
add_to_list(B,T,NT) :-
   %comma_list(B,BL),
   append(B,T,NT).

unify([]).
unify([user(A,B,_,_,_)|R]) :- !, A=B, unify(R).
unify([builtin(A)|R]) :- call(A), unify(R).



