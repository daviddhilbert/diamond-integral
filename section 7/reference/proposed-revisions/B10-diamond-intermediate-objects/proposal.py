"""Batch B10: Definition 6.34, compositions inside muVF^diamond[k] (no referee item).

Independently found during the formalization of Proposition 7.24 (2026-11-20).
The proof of Proposition 7.24 writes an isomorphism as "a sequence of relatively
unary muVF^diamond[k]-morphisms, which exists by definition" and applies
Corollary 7.15 to each arrow. Corollary 7.15 compares standard contractions of
both ends of an arrow, so every intermediate set must be an object of
muVF^diamond[k], with its own proper covariant volume form, and every factor
must be Gamma-measure-preserving. Definition 6.34 does not say this, and a
composition of relatively unary proper covariant homeomorphisms between
definable sets does not supply it: the example added to Remark 6.35 is a
relatively unary proper covariant homeomorphism F of O^2 such that F^{-1} o F
is the identity of (O^2, 0), while no proper covariant form on the middle copy
of O^2 makes F measure-preserving. The definition is made explicit; Remark 6.35
records that composites and inverses stay inside the category, that special
covariant bijections are morphisms with the transported intermediate forms,
and the example. Approved route: author's decision of 2026-11-20 ("fix (1)").

Same format as the batches of Section7/make-review.py (EDITS, RESOLUTIONS,
ANCHORS, TITLE); built here by build-review.py in this folder.
"""

TITLE = 'Section 7 review B10: compositions inside muVF^diamond in Definition 6.34'
ANCHORS = ['Definition 6.34.', 'Corollary 6.37.']

EDITS = [
    (r'The subcategory $\mVF^{\diamond}[k]$ of $\mVF[k]$ consists of the proper invariant objects and the morphisms that are compositions of relatively unary proper covariant homeomorphisms.',
     r'relatively unary proper covariant homeomorphisms.',
     r'''The subcategory $\mVF^{\diamond}[k]$ of $\mVF[k]$ consists of the proper invariant objects and the morphisms that are compositions of relatively unary proper covariant homeomorphisms inside $\mVF^{\diamond}[k]$. Explicitly, a proper invariant object is a pair $\bm A = (A, \omega) \in \mVF[k]$ with $A$ proper invariant and $\omega$ proper covariant, and a morphism $F : \bm A \fun \bm B$ of $\mVF^{\diamond}[k]$ is a composition $F = F_l \circ \cdots \circ F_1$ of $\mVF[k]$-morphisms $F_m : \bm A_m \fun \bm A_{m+1}$, where $\bm A_1 = \bm A$, $\bm A_{l+1} = \bm B$, every $\bm A_m$ is a proper invariant object, and every $F_m$ is a relatively unary proper covariant homeomorphism. Thus each intermediate object carries its own proper covariant volume form, and each factor $F_m$ is itself $\Gamma$-measure-preserving, that is, it satisfies (\ref{cond:mg}) outside a definable set of $\VF$-dimension less than $k$.'''),

    (r'Obviously the composition law holds in  $\mgVF^{\diamond}[k]$',
     r'give various constructions of nontrivial morphisms.',
     r'''Obviously the composition law holds in $\mgVF^{\diamond}[k]$: two such compositions compose to another one, and the identity is the composition with no factors. Moreover, every morphism in it is an honest bijection, as opposed to merely an essential bijection, and is in effect required to admit an inverse: the inverse of each factor $F_m$ is a relatively unary proper covariant homeomorphism $\bm A_{m+1} \fun \bm A_m$ that is again $\Gamma$-measure-preserving, so $F^{-1} = F_1^{-1} \circ \cdots \circ F_l^{-1}$ is a morphism. Thus, $\mgVF^{\diamond}[k]$ is already a groupoid and there is no need to pass to a quotient category as in Remark~\ref{mor:equi}. On the other hand, Proposition~\ref{simplex:with:hole:rvproduct}, Lemma~\ref{spec:inve}, and Remark~\ref{stand:vol} give various constructions of nontrivial morphisms. For a special covariant bijection $T = T_r \circ \cdots \circ T_1$ on a proper invariant object $(A, \omega)$, the intermediate objects are the images $T_i \circ \cdots \circ T_1(A)$ with the transported forms $\omega \circ (T_i \circ \cdots \circ T_1)^{-1}$. Each transported form is proper covariant: on each $\VF$-fiber of $(T_i \circ \cdots \circ T_1)^{-1}$ this follows from the covariance of that fiber, and Lemma~\ref{db:to:db} bounds the radii uniformly over the $\RV$-fibers of the target. Each stage $T_i$ is $\Gamma$-measure-preserving by Lemma~\ref{spec:inve}. Similarly, the lift in Lemma~\ref{L:measure:class:lift} passes through the lifts of the intermediate objects of Lemma~\ref{bijection:partitioned:unary}, whose volume forms factor through their $\RV$-coordinates.

The intermediate objects in Definition~\ref{defn:diamond} cannot be replaced by definable sets without volume forms. Let $t \in \MM$ be definable and nonzero, and let $\kappa : \OO \fun \OO$ be the locally affine homeomorphism that is the identity on $\OO \mi (\MM \cup (1 + \MM))$ and on $\MM \mi t\MM$, and is given by $w \efun tw$ on $t\MM$, by $w \efun t(w - 1)$ on $(1 + \MM) \mi (1 + t\MM)$, and by $w \efun 1 + (w - 1)/t$ on $1 + t\MM$. Then
\[
F(x, z) = \begin{cases} (x, x\kappa(z/x)), & x \neq 0 \text{ and } \vv(z) \geq \vv(x),\\ (x, z), & \text{otherwise},\end{cases}
\]
is a relatively unary proper covariant homeomorphism of $\OO^2$, and $F^{-1} \circ F$ is the identity of $(\OO^2, 0)$. But no proper covariant volume form $\sigma$ on the middle copy of $\OO^2$ makes $F$ $\Gamma$-measure-preserving: by (\ref{cond:mg}), $\sigma \circ F$ would agree almost everywhere with $(x, z) \efun -\vv(\kappa'(z/x))$, which takes the three values $0$ and $\pm \vv(t)$ in every open polydisc around $(0, 0)$, while $F$ is a homeomorphism fixing $(0, 0)$. The proof of Proposition~\ref{kernel:L} applies Corollary~\ref{contraction:same:perm:isp} to each factor $F_m$, and so it needs every $\bm A_m$ to be an object of $\mVF^{\diamond}[k]$.'''),
]

RESOLUTIONS = {}
