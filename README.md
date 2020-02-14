# Prolog reversible debugger

The reversible debugger allows the programmer to explore the derivations of a goal using the cursor keys:

* down: next goal;
* left/right: allows one to explore the different choices of a nondeterministic call;
* up: previous goal in the same derivation.

A typical session looks as follows:

```
$ swipl
?- [rdebug].
true.
?- [example].
true.
?- rdebug(p(X,Y)).
Call: p(A,B)
Exit: p(A,B)
Call: q(A),r(A,B)
Exit: q(a),r(a,A)
Call: r(a,A)
Fail: r(a,A)
```
where the selected call of each goal is underlined, and nondeterministic calls (i.e., calls that match more than one clause) are shown in bold.

Now, if we press the up arrow once, we get back to

```
Call: p(A,B)
Exit: p(A,B)
Call: q(A),r(A,B) 
Exit: q(a),r(a,A)   
```

The debugger is only tested in SWI Prolog.

This is ongoing work. Please send me any comment to <gvidal@dsic.upv.es>