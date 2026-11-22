"""Batch B08a: wording of the application of Lemma 8.9 in the proof of Theorem 8.11.

Follow-up to B08 at the author's request (2026-11-20): the abbreviation
"Write R = ..." introduced to fix an overfull line is removed. Instead the
series Z(sigma')(S) is no longer displayed a second time: the notation I_m of
Lemma 8.9 is used for the lattice points of N I, the lemma is applied to
sigma' directly, and its two conclusions are displayed. The identity
Z([U])(T) = v Z(sigma')(T^N) is justified by m sigma(gamma) = m' sigma'(N delta).
No change of mathematical content.
"""

TITLE = 'Section 8 review B08a: application of Lemma 8.9 in the proof of Theorem 8.11'
ANCHORS = ['be the least positive integer such that', 'no longer needs to go through']

EDITS = [
    (r'is a bijection between $D_m$ and the set of the points of $N I$ in $(m',
     r'''in $(m'^{-1}\Z)^\ell$.''',
     r'''is a bijection between $D_m$ and $(N I)_{m'} = N I \cap (m'^{-1}\Z)^\ell$.'''),

    (r'''with $a_i$, $b$ in $\Z$. Let
\[
Z(\sigma')(S) = \sum_{m' \in \Z^+} \sum_{\delta'}''',
     r'''Since
\[
Z([\bm U])(T) = v Z(\sigma')(T^N),
\]
we conclude that''',
     r'''with $a_i$, $b$ in $\Z$. So Lemma~\ref{lat:zeta} applies to $\sigma'$, the ring $\gmv[[\A]^{-1}]$ and its unit $[\A]$; writing $S$ for the variable, we get
\[
Z(\sigma')(S) \in \gmv[[\A]^{-1}][S]_{\dag} \quad \text{and} \quad \lim_{S \limplies \infty}Z(\sigma')(S) = -\chi(N I) = - \chi(I).
\]
Since $m \sigma(\gamma) = m' \sigma'(N \delta)$ for $m = N m'$, the formula for $(\bm \eta \circ \bm h_m)([\bm U])$ above gives
\[
Z([\bm U])(T) = v \sum_{m' \in \Z^+} \sum_{\delta' \in (N I)_{m'}} [\A]^{-m' \sigma'(\delta')} T^{N m'} = v Z(\sigma')(T^N),
\]
and we conclude that'''),
]

RESOLUTIONS = {}
