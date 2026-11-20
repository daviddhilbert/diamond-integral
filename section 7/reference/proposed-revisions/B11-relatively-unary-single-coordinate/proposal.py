"""Batch B11: Definition 6.24, relatively unary in a single coordinate (no referee item).

Independently found during the formalization of Lemma 7.12 (2026-11-20). The
definition of a relatively unary bijection is stated for a pair of coordinates
(i, j): pr_{j~} o G = pr_{i~}. The sentence after it justifies gluing
piecewise compositions by "identity functions are relatively unary in any
coordinate", which holds for i = j only: the identity is not relatively unary
in the (i, j)-coordinate for i != j. The single-coordinate form is the one of
Definition 5.4 of "Integration in algebraically closed valued fields", where
that sentence is correct. Outside the definition the manuscript never uses a
pair with i != j (the transformations T_i are "(i, i)", Corollary 7.15 is for
"the i-th coordinate", and the proof of Lemma 6.29 adjusts one coordinate at a
time), and neither does the formalization: every step it constructs keeps all
VF-coordinates other than one. Approved route: author's decision of 2026-11-20
("go back to the single-coordinate definition in the paper and in Lean").

The definition is restated for one coordinate, the sentence offering the
alternative "i = j up to coordinate permutations" is removed, and the gluing
sentence is left as it stands.

Same format as the batches of Section7/make-review.py (EDITS, RESOLUTIONS,
ANCHORS, TITLE); built here by build-review.py in this folder.
"""

TITLE = 'Section 7 review B11: relatively unary in a single coordinate'
ANCHORS = ['Definition 6.24.', 'Example 6.25.']

EDITS = [
    (r'A definable bijection $G : A \fun B$ is \memph{relatively unary}, or more precisely,',
     r'holds up to coordinate permutations.',
     r'''A definable bijection $G : A \fun B$ is \memph{relatively unary}, or more precisely, \memph{relatively unary in the $i$th coordinate}, where $i \in [n]$, if $(\pr_{\tilde{i}} \circ G)(x) = \pr_{\tilde{i}}(x)$ for all $x \in A$. If, in addition, $G \rest A_a$ is also a special covariant bijection for every $a \in \pr_{\tilde{i}} (A)$ then $G$ is \memph{relatively special covariant} in the $i$th coordinate.

Let $\bm U = (U, f)$, $\bm V = (V, g)$ be objects of $\RV[k]$. A morphism $F : \bm U \fun \bm V$ is \memph{relatively unary in the $i$th coordinate}, where $i \in [k]$, if $(\pr_{\tilde{i}} \circ g \circ F)(u) = (\pr_{\tilde{i}} \circ f)(u)$ for all $u \in U$.
\end{defn}'''),

    (r'\item relatively unary in the $(i, i)$-coordinate (up to coordinate permutations),',
     r'(up to coordinate permutations),',
     r'''\item relatively unary in the $i$th coordinate,'''),
]

RESOLUTIONS = {}
