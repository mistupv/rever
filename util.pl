%% Some utilities (pretty printing, tracing, etc)

:- module(util,[print_port/3,print_fail_builtin_exception/3,read_keyatom/1,print_solution/2]). 

:- use_module(library(ansi_term)). 
:- use_module(ansi_termx). 

print_solution(G,Env) :-
   ansi_format([bold],"**Solution: ",[]),
   maplist(call,Env),
   format("~w~n",[G]),
   fail.
print_solution(_,_).


%    copy_term((G,Env),(GC,EnvC)),
%    term_variables(GC,GCvars),
%    maplist(call,EnvC),
%    term_variables(G,GVars),
%    print_subs(GVars,GCvars),fail.
% print_solution(_,_) :- !.

% print_subs([],[]) :- nl.
% print_subs([X],[Val]) :- !,
%    print(X),format(" = "),print(Val),nl.
% print_subs([X|R],[Val|RV]) :-
%    print(X),format(" = "),print(Val),format(", "),print_subs(R,RV),!.


% print_solution(G,Env) :-
%    ansi_format([bold],"**Solution: ",[]),
%    copy_term(G,GCC), term_variables(GCC,Vars), numbervars(Vars),
%    %
%    copy_term((G,Env),(Gc,Envc)),
%    term_variables(Gc,VarsG),
%    %numbervars((Gc,Envc)),varnumbers_names((Gc,Envc),(Gc2,Envc2),Bindings),
%    maplist(call,Envc),
%    %unify_bindings(Bindings), 
%    %format(" ~w~n",[Gc2]),
%    numbervars(VarsG),
%    %
%    print_subs(Vars,VarsG),!.

% print_subs([],[]) :- nl.
% print_subs([X],[Val]) :- !,
%    print(X),format(" = "),print(Val),nl.
% print_subs([X|R],[Val|RV]) :-
%    print(X),format(" = "),print(Val),format(", "),print_subs(R,RV),!.

print_port(call,A,Env) :-
   ansi_format([fg(green),bold],"Call: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(builtin_call,A,Env) :-
   ansi_format([fg(green)],"Call: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(redo,A,Env) :-
   ansi_format([fg8(100),bold],"Redo: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(exit,A,Env) :-
   ansi_format([fg(green),bold],"Exit: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(builtin_exit,A,Env) :-
   ansi_format([fg(green)],"Exit: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(fail,A,Env) :-
   ansi_format([fg(red),bold],"Fail: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(builtin_fail,A,Env) :-
   ansi_format([fg(red)],"Fail: ",[]),
   maplist(call,Env),
   format("~w~n",[A]),
   fail.
print_port(_,_,_) :- !.

print_fail_builtin_exception(_A,_Env,Error) :-
   print_message(error,Error),!.
   %ansi_format([fg(blue)],"Exception: ~w~n",[print_message(error,Error)]),!.
   %copy_term((A,Env),(Ac,Envc)),
   %numbervars((Ac,Envc)),varnumbers_names((Ac,Envc),(Ac2,Envc2),Bindings),
   %maplist(call,Envc2),
   %unify_bindings(Bindings), 
   %format("~w~n",[Ac2]),!.

unify_bindings([]).
unify_bindings([Val=Var|R]) :- '$VAR'(Val)=Var,!,unify_bindings(R).
unify_bindings([_|R]) :- unify_bindings(R).

read_key([Code|Codes]) :-
   get_single_char(Code),
   read_pending_codes(user,Codes,[]).

read_keyatom(KAtom) :-
   read_key(Codes),
   codes_keyatom(Codes,KAtom).

codes_keyatom([13],enter)       :- !.
codes_keyatom([115],skip)       :- !.
codes_keyatom([116],trace)       :- !.
codes_keyatom([104],help)       :- !.
codes_keyatom([59],semicolon)   :- !.
codes_keyatom([27,91,65],up)    :- !.
codes_keyatom([27,91,66],down)  :- !.
codes_keyatom([27,91,67],right) :- !.
codes_keyatom([27,91,68],left)  :- !.
codes_keyatom([113],quit)  :- !.
codes_keyatom(_,other)  :- !.


/*

print_goal(G,L) :-
   ansi_format([fg(blue)],"Call: ",[]),
   copy_term((L,G),(LC,GC)), 
   numbervars((LC,GC)),varnumbers_names((LC,GC),(LC2,GC2),Bindings),
   unify(LC2),unify_bindings(Bindings), GC2 = [A|T],
   ansi_format([underline],"~w",[A]),
   (T=[] -> nl
   ; !, comma_list(Tcon,T), format(",~w~n",[Tcon])
   ).

print_goal_nondet(G,L) :-
   ansi_format([fg(blue)],"Call: ",[]),
   copy_term((L,G),(LC,GC)), 
   numbervars((LC,GC)),varnumbers_names((LC,GC),(LC2,GC2),Bindings),
   unify(LC2),unify_bindings(Bindings), GC2 = [A|T],
   ansi_format([underline,bold],"~w",[A]),
   (T=[] -> nl
   ; !, comma_list(Tcon,T), format(",~w~n",[Tcon])
   ).

%print_call(A,L) :-
%   format("Selected call: "),
%   copy_term((L,A),(LCC,ACC)),unify(LCC),numbervars(ACC,0,_),print(ACC),nl.

print_success(G,L) :-
   %format("                                                                                ~n"),
   %cursor_move(1,up),
   ansi_format([fg(green)],"Exit: ",[]),
   copy_term((L,G),(LC,GC)), 
   numbervars((LC,GC)),varnumbers_names((LC,GC),(LC2,GC2),Bindings),
   unify(LC2),unify_bindings(Bindings), GC2 = [A|T],
   ansi_format([],"~w",[A]),
   (T=[] -> !, nl; comma_list(Tcon,T), format(",~w~n",[Tcon])).


print_failure(G,L) :-
   ansi_format([fg(red)],"Fail: ",[]),
   copy_term((L,G),(LC,GC)), 
   numbervars((LC,GC)),varnumbers_names((LC,GC),(LC2,GC2),Bindings),
   unify(LC2),unify_bindings(Bindings), GC2 = [A|T],
   ansi_format([],"~w",[A]),
   (T=[] -> !, nl ; comma_list(Tcon,T), format(",~w~n",[Tcon])).

print_subs([],[]) :- nl.
print_subs([X],[Val]) :- !,
   print(X),format(" = "),print(Val),nl.
print_subs([X|R],[Val|RV]) :-
   print(X),format(" = "),print(Val),format(", "),print_subs(R,RV).

print_solution(InitialGoal,L) :-
   ansi_format([bold],"**Solution",[]),
   copy_term(InitialGoal,GC),term_variables(GC,Vars), numbervars(Vars,0,Next),
   copy_term((L,InitialGoal),(LC,G)),
   term_variables(G,VarsG),
   unify(LC),
   %numbervars(G,0,_),
   comma_list(Goal,GC),
   ansi_format([bold]," [~w]: ",[Goal]),
   numbervars(VarsG,Next,_),
   print_subs(Vars,VarsG).   



trace_history(L) :-
   format("      *trace: "),copy_term(L,LC), numbervars(LC,0,_), print(LC), nl. %%, get_single_char(_).
*/
