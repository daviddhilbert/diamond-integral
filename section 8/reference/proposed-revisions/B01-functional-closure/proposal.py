"""Batch B01: functional closure of henselian substructures (R138).

Independent reading. The paragraph defines "functionally closed" by saying that
the image f(X(M)) is definable in M and then, in a parenthesis, constructible
in M. The parenthesis is false: for M = C((t)) and f(x) = x^2 the image is the
set of squares, whose nonzero elements are those of even valuation, and this
is not the trace of a definable set (a definable subset of VF contains or
omits all nonzero points close enough to 0). What the section uses later
(Lemma 8.2, Lemma 8.3, Lemma 8.6) is only that definable functions with values
in VF and RV send M-rational points to M-rational points, which is the
definition of dcl M = M; the content of the sentence is Lemma 2.3's
equivalence with henselianity. The Gamma-sort is excluded by the paragraph
before (a definable Gamma-valued function may leave Gamma(M)).
"""

TITLE = 'Section 8 review B01: functional closure of henselian substructures'
ANCHORS = ['We begin with a very brief discussion on specialization', 'Notation 8.1.']

EDITS = [
    (r'If $\mathbb{M}$ is definably closed and $\Gamma(\mathbb{M})$ is nontrivial, or equivalently',
     r'This is all we need to deduce the results below.',
     r'''If $\mathbb{M}$ is definably closed and $\Gamma(\mathbb{M})$ is nontrivial, or equivalently (see Lemma~\ref{cut:to:hensel:substru}), the valued field $(\VF(\mathbb{M}), \OO(\mathbb{M}))$  is henselian, then $\mathbb{M}$ is \memph{functionally closed}, that is, for any definable sets $X$, $Y$ (in the sorts $\VF$ and $\RV$, see Terminology~\ref{nota:sub}) and any definable function $f : X \fun Y$, we have $f(X(\mathbb{M})) \sub Y(\mathbb{M})$. In particular, if $f$ is a bijection then, since $f^{-1}$ is definable too, $f$ restricts to a bijection between $X(\mathbb{M})$ and $Y(\mathbb{M})$. The image $f(X(\mathbb{M}))$ is definable in the structure $\mathbb{M}$, but in general it is neither the trace of $f(X)$ nor constructible in $\mathbb{M}$. For instance, if $\mathbb{M} = \C \dpar t$ and $f(x) = x^2$ on $\VF$ then $f(\VF(\mathbb{M}))$ is the set of squares in $\C \dpar t$, whose nonzero elements are the ones of even valuation, whereas a definable subset of $\VF$ either contains or omits all nonzero points that are sufficiently close to $0$. The closure property is all we need to deduce the results below.'''),
]

RESOLUTIONS = {
    '138': r'The constructibility claim is deleted. Functional closure is now stated as the property that is used below: definable functions between definable sets in the sorts $\VF$ and $\RV$ send $\mathbb{M}$-rational points to $\mathbb{M}$-rational points, so definable bijections restrict to bijections of traces. The example of squares in $\C\dpar t$ is recorded in the text.',
}
