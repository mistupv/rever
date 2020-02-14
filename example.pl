p(X,Y) :- q(X), r(X,Y).
q(a).
q(f(X)) :- X is 2+1.
q(c).
r(f(X),f(X)).

