# Prolog reversible debugger

The reversible debugger allows the programmer to explore the derivations of a goal using the cursor keys:

* down: next goal;
* left/right: allows one to explore the different choices of a nondeterministic call;
* up: previous goal in the same derivation.

A typical session looks as follows:

<div>
<pre>
$ swipl
?- [rdebug].
true.
?- [example].
true.
?- rdebug(p(X,Y)).
<span style="color:blue">Call</span>: <u>p(A,B)</u>
<span style="color:green">Exit</span>: p(A,B)
<span style="color:blue">Call</span>: <u><b>q(A)</b></u>,r(A,B)
<span style="color:green">Exit</span>: q(a),r(a,A)
<span style="color:blue">Call</span>: <u>r(a,A)</u>
<span style="color:red">Fail</span>: r(a,A)
</pre>
</div>
where the selected call of each goal is underlined, and nondeterministic calls (i.e., calls that match more than one clause) are shown in bold.

Now, if we press the up arrow once, we get back to

<div>
<pre>
<span style="color:blue">Call</span>: <u>p(A,B)</u>
<span style="color:green">Exit</span>: p(A,B)
<span style="color:blue">Call</span>: <u><b>q(A)</b></u>,r(A,B)
<span style="color:green">Exit</span>: q(a),r(a,A)
</pre>
</div>

A successful derivation looks as follows:
<div>
<pre>
<span style="color:blue">Call</span>: <u>p(A,B)</u>
<span style="color:green">Exit</span>: p(A,B)
<span style="color:blue">Call</span>: <u><b>q(A)</b></u>,r(A,B)
<span style="color:green">Exit</span>: q(f(A)),r(f(A),B)
<span style="color:blue">Call</span>: <u>A is 2+1</u>,r(f(A),B)
<span style="color:green">Exit</span>: 3 is 2+1,r(f(3),A)
<span style="color:blue">Call</span>: <u>r(f(3),A)</u>
<span style="color:green">Exit</span>: r(f(3),f(3))
<b>**Solution [p(A,B)]:</b> A = f(3), B = f(3)
</pre>
</div>

The debugger is only tested in SWI Prolog.

This is ongoing work. Please send me any comment to <gvidal@dsic.upv.es>