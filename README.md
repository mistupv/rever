# Rever. A Prolog reversible debugger

The reversible debugger **rever** allows the programmer to explore the derivations of a goal using the cursor keys:

* down (or Enter): next goal;
* up: previous goal in the SLD tree;

as well as a number of standard keys

* ";" (semicolon): alternative solutions (as in Prolog);
* s (skip): runs continuously until the next failure/sucess
* q (quit): to stop the debugging session.

A typical session looks as follows:

<div>
<pre>
$ swipl
?- [rever].
true.

?- [ex].
true.

?- rtrace(p(A,B)).
Call: p(A,B)
Call: q(A)
Exit: q(a)
Call: r(a,B)
Fail: r(a,B)
Redo: q(A)
Exit: q(b)
Call: r(b,B)
Exit: r(b,b)
Exit: p(b,b)
**Solution: A = b, B = b
Redo: r(b,B)
Exit: r(b,c)
Exit: p(b,c)
**Solution: A = b, B = c</pre>
</div>
At any point, the user can go backwards pressing the up arrow.

The debugger is only tested in SWI Prolog.

This is ongoing work. Please send me any comment to <gvidal@dsic.upv.es>