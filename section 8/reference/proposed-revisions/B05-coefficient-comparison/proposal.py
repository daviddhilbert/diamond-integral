"""Batch B05: Lemma 8.6, the coefficient comparison (R145, R146, R173).

Independent reading of the proof.
1. "we can choose apertures (gamma_i, t_i) with gamma_i in m^{-1}Z so that F
   induces a definable bijection between A[m; beta] and LU[m; beta] for all
   sufficiently large beta". Two problems.
   (a) Definition 6.11 now has aperture functions tau on the retained labels;
       there is nothing to choose. At a label rational over C((t^{1/m})) the
       endpoint tau(u) and the cutoff are rational by functional closure.
   (b) The claim is false for arbitrary large beta. Checked example (m = 1):
       A = (1 + t + M_2) x (t + M_3), focus lambda(y) = y/t, which is
       (3, 2)-covariant. The points (1 + t, t) and (1 + t, t + t^{N+1}) have
       the same truncation for the cutoffs (N, N), and their images under the
       shear differ by t^N in the first coordinate, which is not in M_N. For
       cutoffs with beta_y >= beta_x + 1 the shear does induce a bijection.
   Repair: each centripetal step changes one coordinate by a continuous
   function of the others. Choose the cutoff of the changed coordinate first
   and the cutoffs of the other coordinates large relative to it; then the
   step and its inverse induce maps on truncations. The cutoffs depend on the
   step, which is harmless because tilde A[m] does not depend on beta
   (Lemma 8.5). No single beta for the whole composition is needed (or
   available in general: successive steps may need opposite orderings).
2. "we may further assume that D is trivial or even vrv(U) is a singleton":
   finite additivity does not reduce a positive-dimensional vrv(U) to a
   point. For fixed m only the finitely many lattice values matter, and the
   computation on LU is direct.
3. The right-hand side is defined for A inside O^n x RV^l only. The
   assumption is added; it is preserved by every step (the focus lies in the
   RV-disc of the changed coordinate, and the endpoint has value >= 0), and
   LU lies in O^n when A does. It covers the application (the Milnor tube).

The stale terms (Gamma-cohesive bipolar twistoid decomposition) disappear.
Depends on B02 (Lemma 8.2), B03 (target J_var) and B04 (L_gamma, !K RES).
"""

TITLE = 'Section 8 review B05: the coefficient comparison of Lemma 8.6'
ANCHORS = ['Lemma 8.6.', 'Bounded version']

EDITS = [
    (r'Suppose that $(A, 0) \in \mgVF^\diamond[n]$. Then, in',
     r'Then, in',
     r'Suppose that $(A, 0) \in \mgVF^\diamond[n]$ and $A \sub \OO^n \times \RV^l$. Then, in'),

    (r'''\begin{proof}
By Lemma~\ref{L:measure:surjective}, there exists a special covariant bijection $F : (A, 0) \fun (\bb L \bm U, 0)$''',
     r'''Then the equality follows from a simple computation.
\end{proof}''',
     r'''\begin{proof}
We first show that $\tilde A[m]$ is not changed by the operations that make up a special covariant bijection. So let $A \sub \OO^n \times \RV^l$ be doubly bounded, proper invariant and regularized, and let $\eta^\flat : A \fun A^\flat$ be a lifted centripetal transformation as in Definition~\ref{defn:special:bijection}, followed by regularization. Write a point of $A$ as $(a, x)$, where $a$ is the first $\VF$-coordinate, and suppress the $\RV$-labels. On its two branches $\eta^\flat$ is given by
\[
(a, x) \efun (a - \lambda(x), x), \qquad (a, x) \efun (a - \lambda(x) + b(x), x),
\]
according to whether $\vv(a - \lambda(x)) \leq \gamma_\gp$ or not, and the image carries the $\RV$-label of its first coordinate and the tag of the branch. Since $a$ and $\lambda(x)$ lie in the same $\RV$-disc and $\vv(b(x)) = \gamma_\gp \geq 0$, we have $A^\flat \sub \OO^n \times \RV^{l'}$.

Choose $\beta = (\beta_1, \beta') \in (m^{-1}\Z)^n$ as follows. Both $A$ and $A^\flat$ are proper invariant (Lemmas~\ref{spec:inve} and~\ref{conv:unif}), and hence $\epsilon$-invariant for every sufficiently large $\epsilon \in \Gamma$. First take $\beta_1$ so large that $\beta_1 \geq \gamma_\gp$ for every $\gp$ and that $A$ and $A^\flat$ are $\beta_1$-invariant. The functions $\lambda$ and $b$ are continuous and, over each label, their domains are closed and bounded. So, as in the proof of Lemma~\ref{conti:covar}, there is a $\delta \in \Gamma$ such that every $\VF$-fiber of $\lambda$ and of $b$ is $(\delta, \beta_1)$-covariant. Then take every coordinate of $\beta'$ at least $\delta$ and at least $\beta_1$, and so large that the labels of $A$ and of $A^\flat$ are constant on their open polydiscs of radius $\beta$. Then $A$ and $A^\flat$ are $\beta$-invariant.

Let $(a, x)$, $(a', x')$ be two points of $A$ with the same labels such that $a - a' \in \MM_{\beta_1}$ and $x - x' \in \MM_{\beta'}$. Then $\lambda(x) - \lambda(x') \in \MM_{\beta_1}$ and $b(x) - b(x') \in \MM_{\beta_1}$. Since $\beta_1 \geq \gamma_\gp$, the two points lie on the same branch, the first coordinates of their images differ by an element of $\MM_{\beta_1}$, and these have the same $\RV$-label, because their values are at most $\gamma_\gp$. The inverse of $\eta^\flat$ adds $\lambda(x)$, and subtracts $b(x)$ on the second branch, so it has the same property. Since $\eta^\flat$ and its inverse are definable and $\C \dpar{t^{1/m}}$ is functionally closed, $\eta^\flat$ induces a bijection between $A[m;\beta]$ and $A^\flat[m;\beta]$. Hence $\tilde A[m] = \widetilde{A^\flat}[m]$. Note that, for a given $\beta_1$, the other cutoffs $\beta'$ have to be large enough: in general $\eta^\flat$ does not induce a map between the truncations for an arbitrary large $\beta$. This is harmless, since $\tilde A[m]$ does not depend on $\beta$.

The same argument, with no focus, applies to regularization and to the preliminary translations in Remark~\ref{spec:addendum}.

By Lemma~\ref{L:measure:surjective}, there exists a special covariant bijection $F : (A, 0) \fun (\bb L \bm U, 0)$, where $\bm U = (U, f) \in \RV^{\db}[n]$, and then $\int^\diamond [(A, 0)] = [(U, f, 0)] / J_{\mathrm{var}}$. By the above, $\tilde A[m] = \widetilde{\bb L \bm U}[m]$. Thus, we may assume that $A$ is already of the form $\bb L \bm U$.

Let $U^{(m)}$ be the set of those $u \in U$ such that $\vrv(u)$ is a tuple in $m^{-1}\Z$. The points of $\bb L \bm U$ that are rational over $\C \dpar{t^{1/m}}$ lie over $U^{(m)}$. There is a finite definable partition of $U^{(m)}$ such that, on each piece $R$, the tuple $\vrv \circ f$ is constant, say with value $\alpha = (\alpha_1, \ldots, \alpha_n) \in (m^{-1}\Z)^n$, where $\alpha_i \geq 0$. Take $\beta_i \geq \alpha_i$ for all $i$ and all pieces. Over a point $u \in R$, the $i$th $\VF$-coordinate of a rational point of $\bb L \bm U$ has no terms below $t^{\alpha_i}$, its coefficient of $t^{\alpha_i}$ is $f_i(u)$, and its coefficients of $t^\gamma$, $\alpha_i < \gamma \leq \beta_i$, are unrestricted. So the part of $\bb L \bm U[m;\beta]$ over $R$ is in definable bijection with $R \times \prod_i \prod_\gamma L_\gamma$, where $\gamma$ runs through the $m(\beta_i - \alpha_i)$ elements of $m^{-1}\Z$ with $\alpha_i < \gamma \leq \beta_i$, and its class in $\sggk \RES$ is $[R] [\A]^{m \Sigma (\beta - \alpha)}$. Therefore
\[
\Theta(\widetilde{\bb L \bm U}[m]) = \sum_R \Theta([R]) [\A]^{-m \Sigma \alpha}.
\]
On the other hand, the weight of $(U, f, 0)$ on $R$ is $\Sigma \alpha$, and so, by Lemma~\ref{muhat:section}, the right-hand side is $(\bm \eta \circ \bm h_m)([(U, f, 0)])$.
\end{proof}'''),
]

RESOLUTIONS = {
    '145': r'The assumption $A\sub\OO^n\times\RV^l$ is added to the lemma. The proof notes that it is preserved by every step of a special covariant bijection. It covers the application to $\mdl X_f$.',
    '146': r'The reduction to a singleton is replaced by the computation for the fixed $m$: only the finitely many lattice values of $\vrv(U)$ contribute, and on a piece with $\vrv\circ f=\alpha$ the normalized class is $\Theta([R])[\A]^{-m\Sigma\alpha}$. No choice of apertures is made: with the aperture functions of Definition~\ref{defn:special:bijection}, the endpoints at labels rational over $\C\dpar{t^{1/m}}$ are rational by functional closure.',
    '173': r'The proof now treats one centripetal step at a time. The cutoff of the changed coordinate is chosen first and the other cutoffs are taken large relative to it, by the continuity of the focus and of the lift; then the step and its inverse induce maps between the truncations. The cutoffs depend on the step, and the independence of $\tilde A[m]$ from $\beta$ is used. The proof records that an arbitrary large $\beta$ does not work.',
}
