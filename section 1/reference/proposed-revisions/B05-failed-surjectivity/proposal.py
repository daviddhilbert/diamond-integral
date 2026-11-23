"""Batch B05: an explicit object outside the images of the tensor morphisms (R013).

Independent reading. Hrushovski-Loeser, arXiv:1111.1954v2, Section 8.1 (pp. 27-29): the objects
of vol RV[n] are those of RV[n], pairs (X, f) with f : X -> RV^n finite-to-one; a morphism is a
definable bijection h with w(f(x)) = w(f'(h(x))), w = sum of vrv of the coordinates. vol RES[n]
is the full subcategory of objects in RES[n]; vol Gamma^bdd, vol Gamma^2bdd consist of the sets
bounded below, bounded. (8.1.4), (8.1.6), (8.1.7) are the maps
K+(vol RES[*]) (x) K+(vol Gamma^?[*]) -> K+(vol RV^?[*]) induced by ((W, g), Delta) ->
(W x Delta^sharp, g x id); for (8.1.7) they cite HK Proposition 10.10. HK, arXiv:math/0510133v3,
Proposition 10.10(2) (p. 95) asserts that K+(RES_{Gamma-vol}[*]) (x) K+(vol Gamma[*]) ->
K+(RV_{Gamma-vol}[*]) is an isomorphism; by HK Definition 5.21 its morphisms are the bijections
with Jcb_Gamma = 0, the same condition. The surjectivity proof given for (2) is "similar" to
(1), where the volume form is free data; in (2) the weight is tied to f.

By Notation jcbG:op, w-preserving bijections are exactly the muRV morphisms between objects with
volume form 0.

The object: X = {u in RV : 0 < vrv(u) < 1}, f(u) = u^2, an object of vol RV^2bdd[1]. Proof that it
is not a class of a disjoint union of products: work over S = C((t)); for m a multiple of a common
ramification index N of the finite RES[0] factors, functional closure of C((t^{1/m})) gives a
weight-preserving bijection of the rational points. Rational weights on X are 2i/m (0 < i < m),
never 1/m. The point rv(t^{1/m}) has weight 2/m; for m large it must land in a product W x Delta^sharp
with W finite and (0, 2/m] inside Delta, and then (p, rv(t^{1/m})) is a rational point of weight
1/m. Contradiction. In muRV the identity is an isomorphism (X, f, 0) -> (X, id, vrv) (the
Gamma-Jacobian of the correspondence is -2 vrv(u) + vrv(u)), which is in the image of mu Psi.

Placement: the example goes into the existing remark of Section 8 that cites HK 10.10(2), so no
result is renumbered; the remark gets a label. The introduction and the comment after
Proposition red:D:iso refer to it.
"""

TITLE = 'Section 1 review B05: the failed surjectivity'
ANCHORS = ['contrary to what is claimed in', 'Identify the failed surjectivity explicitly',
           'does not hold; see Remark', 'the volume form absorbs the difference', 'One of the key steps of the main construction']
SELECT = True

EXAMPLE = r'''Unfortunately, this result does not hold, and neither do the surjectivity claims for the morphisms (8.1.4), (8.1.6) and (8.1.7) of \cite{hru:loe:lef}. Here is an explicit object outside their images.

Recall from \cite[\S~8.1]{hru:loe:lef} that the objects of $\mathrm{vol}\RV[n]$ are the objects $(X, f)$ of $\RV[n]$, and that a morphism $(X, f) \fun (X', f')$ is a definable bijection $h : X \fun X'$ such that $w(f(x)) = w(f'(h(x)))$ for all $x \in X$, where $w(y_1, \ldots, y_n) = \vrv(y_1) + \cdots + \vrv(y_n)$. By Notation~\ref{jcbG:op}, these are exactly the morphisms of $\mgRV[n]$ between objects with the constant volume form $0$. The category $\mathrm{vol}\RES[n]$ is the full subcategory of the objects in $\RES[n]$, and the morphisms in question are induced by $((W, g), \Delta) \efun (W \times \Delta^\sharp, g \times \id)$, where $\Delta \sub \Gamma^l$ is definable. So every class in their images is the class of a finite disjoint union $Y$ of such products. The categories in \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf} have the same morphisms \cite[Definition~5.21]{hrushovski:kazhdan:integration:vf}.

Let $X = \set{u \in \RV \given 0 < \vrv(u) < 1}$ and $f(u) = u^2$, so that $(X, f)$ is an object of $\mathrm{vol}\RV[1]$ whose image in $\Gamma$ is doubly bounded. Suppose that $h : (X, f) \fun Y$ is an isomorphism in $\mathrm{vol}\RV[1]$, with $Y$ as above. Since the degree is $1$, every product in $Y$ is of one of two kinds: either $W \in \RES[1]$ and $l = 0$, and then the weight $w \circ (g \times \id)$ takes only finitely many values on it, all in $\Q$; or $W \in \RES[0]$, that is, $W$ is finite, and $\Delta \sub \Gamma$, and then the point $(p, y)$ has weight $\vrv(y)$. The points of the finite sets $W$ lie in the model $\puC$ of $\ACVF(0,0)$, so they all lie in $\RV(\C\dpar{t^{1/N}})$ for some $N \in \Z^+$. Each $\Delta$ is a finite union of points and intervals with endpoints in $\Q \cup \{\pm\infty\}$. Choose a multiple $m$ of $N$ such that $2/m$ is smaller than every positive endpoint of the sets $\Delta$ and every positive weight on the products of the first kind.

Since $\C\dpar{t^{1/m}}$ is functionally closed, $h$ restricts to a weight-preserving bijection between the points of $X$ and of $Y$ that are rational over $\C\dpar{t^{1/m}}$. The weights of the rational points of $X$ are the numbers $2i/m$ with $0 < i < m$; in particular, no rational point of $X$ has weight $1/m$. The rational point $\rv(t^{1/m})$ of $X$ has weight $2/m$, so its image lies in a product $W \times \Delta^\sharp$ of the second kind with $2/m \in \Delta$. By the choice of $m$, $(0, 2/m] \sub \Delta$, hence $1/m \in \Delta$, and for any $p \in W$ the point $(p, \rv(t^{1/m}))$ of $Y$ is rational over $\C\dpar{t^{1/m}}$ and has weight $1/m$. This is a contradiction. Therefore $[(X, f)]$ is not in the image of (8.1.4), (8.1.6) or (8.1.7) of \cite{hru:loe:lef}, nor in the image of the map in \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf}.

In the category $\mgRV[1]$ of this paper, by contrast, the identity of $X$ is an isomorphism from $(X, f, 0)$ onto $(X, \id, \vrv)$, which lies in the image of ${\mu}\Psi$ (Proposition~\ref{red:D:iso}): the volume form absorbs the difference of the weights, whereas in $\mathrm{vol}\RV[1]$ the weight is tied to the structural map.'''

EDITS = [
    ('\\begin{rem}\nOne of the key steps of the main construction',
     '\\begin{rem}\nOne of the key steps of the main construction',
     '\\begin{rem}\\label{rem:HK:fail}\nOne of the key steps of the main construction', False),
    (r'We have pointed out above that, unfortunately, this result does not hold.',
     r'We have pointed out above that, unfortunately, this result does not hold.',
     EXAMPLE),
    (r'contrary to what is claimed in \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf}, make their construction',
     r'make their construction',
     r'''contrary to what is claimed in \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf} (see Remark~\ref{rem:HK:fail} for an explicit object outside their images), make their construction'''),
    (r'Note that, however, \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf} does not hold.',
     r'Note that, however, \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf} does not hold.',
     r'''Note that, however, \cite[Proposition~10.10(2)]{hrushovski:kazhdan:integration:vf} does not hold; see Remark~\ref{rem:HK:fail}.'''),
]

RESOLUTIONS = {
    '013': r'Remark~\ref{rem:HK:fail} now gives an explicit object, $X = \set{u \in \RV \given 0<\vrv(u)<1}$ with $f(u) = u^2$, of $\mathrm{vol}\RV[1]$ outside the images of (8.1.4), (8.1.6) and (8.1.7) of Hrushovski--Loeser and of the map in Hrushovski--Kazhdan, Proposition~10.10(2), with a proof by the weights of the points rational over $\C\dpar{t^{1/m}}$. The introduction and the comment after Proposition~\ref{red:D:iso} refer to it; no result is renumbered.',
}
