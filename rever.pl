:- use_module(iso_predicates).
:- use_module(prolog_code).
:- use_module(ansi_termx). 
:- use_module(util).

:- dynamic notrace/0.
:- dynamic noshow/0.

% main call (tracer):
rtrace(G) :- 
   comma_list(G,[A|T]),
   retractall(notrace),
   retractall(noshow),
   solve([A|T],[],bot,[],[],[A|T]).

% main call (debugger):
rdebug(G) :- 
   comma_list(G,[A|T]),
   retractall(notrace), assert(notrace),
   retractall(noshow), assert(noshow),
   solve([A|T],[],bot,[],[],[A|T]).

%% "bot" means no clause label!!

%%%%%%%%%%%%%%%%%%%
%% forward calculus

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%for debugging:
% print_history([]).
% print_history([rtrace|R]) :-
%   print(rtrace),write(","),print_history(R).
% print_history([bck(_G,_Env)|R]) :-
%   print(bck),write(","),print_history(R).
% print_history([next(_Env)|R]) :-
%   print(next),write(","),print_history(R).
% print_history([fail(_A)|R]) :-
%   print(fail),write(","),print_history(R).
% print_history([ch(_N)|R]) :-
%   print(ch),write(","),print_history(R).
% print_history([unf(_A,_Env,_Cl,_Blen)|R]) :-
%   print(unf),write(","),print_history(R).
% print_history([exit(_A)|R]) :-
%   print(exit),write(","),print_history(R).
% print_history([builtin(_A,_Env)|R]) :-
%   print(fail),write(","),print_history(R).

% solve(_Goal,_Env,_Cl,_Alts,History,_InitialGoal) :-
%   print_history(History), fail.

% solve(Goal,Env,Cl,Alts,History,InitialGoal) :-
%   print(solve(Goal,Env,Cl,Alts,History,InitialGoal)),write(" "),fail.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% failure
solve([fail|T],Env,bot,[],History,InitialGoal) :-
  !,
  format("~nNo more solutions...~n",[]),read_keyatom(Key),
  (Key=up ->       !, retractall(notrace),retractall(noshow),
                      bsolve([fail|T],Env,bot,[],History,InitialGoal)
   ; Key=quit ->     !, abort                      
   ; true
   ).

% next solution (there are alternatives)
solve([],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal) :-
  !,
  print_solution(InitialGoal,Env),
  %retractall(notrace),
  read_keyatom(Key1),
  (Key1=trace -> !, retractall(noshow),retractall(notrace),
                    print_redo(A,Env2),
                    read_keyatom(Key2),
                    (Key2=enter -> !, solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                    ; Key2=down -> !, solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                    ; Key2=up ->   !, retractall(notrace),retractall(noshow),
                                      solve([],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal)
                    ; Key2=skip ->   !, retractall(notrace), assertz(notrace),
                                        solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                    ; Key2=quit ->     !, abort                    
                    ; solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                    )
   ; Key1=semicolon -> !, (noshow,! ; print_redo(A,Env2)),
                        (notrace, !, Key2=enter ; read_keyatom(Key2)),
                        !,
                        (Key2=enter -> !, solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                        ; Key2=down -> !, solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                        ; Key2=up ->   !, retractall(notrace),retractall(noshow),
                                          solve([],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal)
                        ; Key2=skip ->   !, retractall(notrace), assertz(notrace),
                                            solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                        ; Key2=quit ->     !, abort                    
                        ; solve([A|T2],Env2,Cl,Alts,[bck([fail|T2],Env2),next(Env)|History],InitialGoal)
                        )
    ; Key1=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),bsolve([],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal)
    ; Key1=quit ->  !, abort
    ; cursor_move(1,up),
      solve([],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal)
   ).

% next solution (no alternatives)
solve([],Env,bot,[],History,InitialGoal) :-
  !,
  print_solution(InitialGoal,Env),
  format("No more solutions...~n",[]),
  read_keyatom(Key),
  (Key=up ->   !, retractall(notrace),retractall(noshow),
                  print(^),bsolve([],Env,bot,[],History,InitialGoal)
    ; Key=quit ->  !, abort
    ; cursor_move(2,up),
      solve([],Env,bot,[],History,InitialGoal)
   ).


% backtrack
solve([fail|T],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal) :-
  (noshow, ! ; print_redo(A,Env2)),
  (notrace, !, Key=enter ; read_keyatom(Key)),
  !,
  (Key=enter -> !, solve([A|T2],Env2,Cl,Alts,[bck([fail|T],Env)|History],InitialGoal)
    ; Key=down -> !, solve([A|T2],Env2,Cl,Alts,[bck([fail|T],Env)|History],InitialGoal)
    ; Key=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),bsolve([fail|T],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal)
    ; Key=skip ->   !, retractall(notrace), assertz(notrace),
                       solve([A|T2],Env2,Cl,Alts,[bck([fail|T],Env)|History],InitialGoal)
    ; Key=quit ->  !, abort
    ; solve([A|T2],Env2,Cl,Alts,[bck([fail|T],Env)|History],InitialGoal)
   ).

% exit
solve([ret(A)|T],Env,bot,Alts,History,InitialGoal) :-
  !,  %% moved this case here to avoid considering choice_fail for ret(A) 
  (noshow, !; print_exit(A,Env)),
  (notrace, !, Key=enter ; read_keyatom(Key)),
  (Key=enter -> !, solve(T,Env,bot,Alts,[exit(A)|History],InitialGoal)
    ; Key=down -> !, solve(T,Env,bot,Alts,[exit(A)|History],InitialGoal)
    ; Key=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),bsolve([ret(A)|T],Env,bot,Alts,History,InitialGoal)
    ; Key=skip ->   !, retractall(notrace), assertz(notrace),
                       solve([ret(A)|T],Env,bot,Alts,History,InitialGoal)
    ; Key=quit ->  !, abort
    ; solve(T,Env,bot,Alts,[exit(A)|History],InitialGoal)
   ).

%% choice rtrace
solve([rtrace|T],Env,Cl,Alts,History,InitialGoal) :-
  !,
  retractall(notrace),retractall(noshow),
    solve(T,Env,Cl,Alts,[rtrace|History],InitialGoal).

%% choice (built-in)
solve([A|T],Env,bot,Alts,History,InitialGoal) :-
  (iso_builtin_predicate(A) ; predicate_property(A,imported_from(_))),
  !,
  (noshow,!; print_call_builtin(A,Env)),
  (notrace, !, Key1=enter ; read_keyatom(Key1)),
  (Key1=enter -> !, solve_builtin([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=down -> !, solve_builtin([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),bsolve([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=skip ->  !, retractall(notrace), assertz(notrace),
                      solve_builtin([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=quit ->  !, abort
    ; solve_builtin([A|T],Env,bot,Alts,History,InitialGoal)
  ).

%% choice 
solve([A|T],Env,bot,Alts,History,InitialGoal) :-
  matching_clauses(A,Env,[_|_]), % matches at least one clause
  !,
  (noshow,!; print_call(A,Env)),
  (notrace, !, Key=enter ; read_keyatom(Key)),
  (Key=enter -> !, solve_choice([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key=down -> !, solve_choice([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),bsolve([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key=skip ->  !, retractall(notrace), assertz(notrace),
                      solve_choice([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key=quit ->  !, abort
    ; solve_choice([A|T],Env,bot,Alts,History,InitialGoal)
  ).

%% choice fail 
solve([A|T],Env,bot,Alts,History,InitialGoal) :-
  matching_clauses(A,Env,[]),!, %% no matching clause!
  (noshow,! ; print_call(A,Env)),
  (notrace, !, Key1=enter ; read_keyatom(Key1)),
  (Key1=enter -> !, solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=down -> !, solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=up ->   !, retractall(notrace),retractall(noshow),
                      print(^),bsolve([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=skip ->   !, retractall(notrace), assertz(notrace),
                       solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key1=quit ->  !, abort
    ; solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
   ).


% unfold

solve([A|T],Env,Cl,Alts,History,InitialGoal) :-
  not(Cl=bot),!,
  clause(H,B,Cl), %% checking unifiability is not needed... 
  comma_list(B,Blist),
  add_to_list(Blist,[ret(A)|T],NT),   %% we add ret(A) to print "exit"
  size(Blist,Blen),
  unifiable(A,H,MGU),
  append(Env,MGU,NewEnv),
  solve(NT,NewEnv,bot,Alts,[unf(A,Env,Cl,Blen)|History],InitialGoal).

%% some auxiliary predicates:

solve_builtin([A|T],Env,bot,Alts,History,InitialGoal) :-
  copy_term((A,Env),(Ac,Envc)),
  maplist(call,Envc),
  catch(Ac,Error,solve_builtin_exception(Error,[A|T],Env,bot,Alts,History,InitialGoal)),
  !,
  unifiable(A,Ac,MGU),
  append(Env,MGU,NewEnv),
  (noshow,! ; print_exit_builtin(A,NewEnv)),
  (notrace, !, Key2=enter ; read_keyatom(Key2)),
  (Key2=enter -> !, solve(T,NewEnv,bot,Alts,[builtin(A,Env)|History],InitialGoal)
    ; Key2=down -> !, solve(T,NewEnv,bot,Alts,[builtin(A,Env)|History],InitialGoal)
    ; Key2=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),solve([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key2=skip ->  !, retractall(notrace), assertz(notrace),
                      solve(T,NewEnv,bot,Alts,[builtin(A,Env)|History],InitialGoal)
    ; Key2=quit ->  !, abort
    ; solve(T,NewEnv,bot,Alts,[builtin(A,Env)|History],InitialGoal)
  ).

solve_builtin([A|T],Env,bot,Alts,History,InitialGoal) :-
  (noshow,! ; print_fail_builtin(A,Env)),
  (notrace, !, Key2=enter ; read_keyatom(Key2)),
  (Key2=enter -> !, solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key2=down -> !, solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key2=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),solve([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key2=skip ->  !, retractall(notrace), assertz(notrace),
                      solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
    ; Key2=quit ->  !, abort
    ; solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal)
  ).

solve_builtin_exception(Error,[A|T],Env,bot,Alts,History,InitialGoal) :-
  retractall(noshow),
  retractall(notrace),
  print_fail_builtin_exception(A,Env,Error),
  read_keyatom(Key2),
  (Key2=up ->   !, retractall(notrace),retractall(noshow),
                   print(^),solve([A|T],Env,bot,Alts,History,InitialGoal)
  ; Key2=quit -> !, abort
  ; cursor_move(2,up),
    solve_builtin_exception(Error,[A|T],Env,bot,Alts,History,InitialGoal)
  ).


solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal) :-
  (noshow, !; print_fail(A,Env)),
  (notrace, !, Key2=enter ; read_keyatom(Key2)),
  (Key2=enter -> !, solve([fail|T],Env,bot,Alts,[fail(A)|History],InitialGoal)
   ; Key2=down -> !, solve([fail|T],Env,bot,Alts,[fail(A)|History],InitialGoal)
   ; Key2=up ->   !, retractall(notrace),retractall(noshow),
                     print(^),solve([A|T],Env,bot,Alts,History,InitialGoal)
   ; Key2=skip -> !, retractall(notrace), assertz(notrace),
                     solve([fail|T],Env,bot,Alts,[fail(A)|History],InitialGoal)
   ; Key2=quit ->  !, abort
   ; solve([fail|T],Env,bot,Alts,[fail(A)|History],InitialGoal)                  
  ).

solve_choice([A|T],Env,bot,Alts,History,InitialGoal) :-
  matching_clauses(A,Env,[Cl|Clauses]),!, %% at least one matching clause!
  create_alts([A|T],Env,Clauses,AAlts),
  append(AAlts,Alts,NewAlts),
  length([Cl|Clauses],N),
  solve([A|T],Env,Cl,NewAlts,[ch(N)|History],InitialGoal).


matching_clauses(A,Env,Clauses) :- 
   copy_term((A,Env),(Ac,Envc)),
   maplist(call,Envc),
   findall(Ref,clause(Ac,_,Ref),Clauses).

create_alts(_G,_Env,[],[]).
create_alts(G,Env,[Ref|R],[(G,Env,Ref)|RR]) :- create_alts(G,Env,R,RR).

%%%%%%%%%%%%%%%%%%%%
%% backward calculus

% this is just to avoid going backwards from the initial goal...
bsolve(G,[],bot,[],[],H) :-
  !,
  cursor_move(1,up),
  solve(G,[],bot,[],[],H).

% this only for the case: (rtrace,G) as initial goal
bsolve(G,[],bot,[],[rtrace],H) :-
  !,
  cursor_move(1,up),
  solve(G,[],bot,[],[rtrace],H).

% % next solution (there are alternatives)
% bsolve([A|T2],Env2,Cl,Alts,[next(Env)|History],InitialGoal) :- 
%   !,
%   solve([],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal).

% next solution (there are alternatives)
bsolve([fail|_],_Env,_Cl,Alts,[next(Env)|History],InitialGoal) :- 
  !,
  solve([],Env,bot,Alts,History,InitialGoal).

% backtrack
bsolve([A|T2],Env2,Cl,Alts,[bck([fail|T],Env)|History],InitialGoal) :-
  !,
  solve([fail|T],Env,bot,[([A|T2],Env2,Cl)|Alts],History,InitialGoal).

% exit
bsolve(T,Env,bot,Alts,[exit(A)|History],InitialGoal) :-
  !, 
  solve([ret(A)|T],Env,bot,Alts,History,InitialGoal).

%% rtrace
bsolve(T,Env,Cl,Alts,[rtrace|History],InitialGoal) :-
  !,
  solve([rtrace|T],Env,Cl,Alts,History,InitialGoal).

  
%% choice built-in:
bsolve(T,_NewEnv,bot,Alts,[builtin(A,Env)|History],InitialGoal) :-
  !,
  solve_builtin([A|T],Env,bot,Alts,History,InitialGoal).

%% choice 
bsolve([A|T],Env,_Cl,NewAlts,[ch(N)|History],InitialGoal) :-
  !,
  M is N-1,
  length(AAlts,M),
  append(AAlts,Alts,NewAlts),
  solve([A|T],Env,bot,Alts,History,InitialGoal).

%% choice fail 
bsolve([fail|T],Env,bot,Alts,[fail(A)|History],InitialGoal) :-
  !,
  solve_choice_fail([A|T],Env,bot,Alts,History,InitialGoal).

% unfold
bsolve(NT,_NewEnv,bot,Alts,[unf(A,Env,Cl,Blen)|History],InitialGoal) :-
  !,
  length(Blist,Blen),
  append(Blist,[ret(A)|T],NT),
  bsolve([A|T],Env,Cl,Alts,History,InitialGoal).




% some utility predicates:

add_to_list([true],T,T) :- !.
add_to_list(B,T,NT) :-
   append(B,T,NT).

size([true],0) :- !.
size(L,N) :- length(L,N).


