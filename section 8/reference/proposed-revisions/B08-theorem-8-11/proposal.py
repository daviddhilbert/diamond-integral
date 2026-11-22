"""Batch B08: Remark 8.10 and the proof of Theorem 8.11 (R154).

Independent reading of the proof.
- "bipolar twistoid", tbk: replaced by a monomial piece h_M(U) = V x I^sharp
  (Lemma 5.12) and v = Theta([V])[G_m]^l, as in batch B02.
- "(P_Gamma)" becomes J_var (batch B03).
- "By Remark 3.15, sigma is Z-linear": the remark (as approved) says piecewise
  Z-affine with constant terms values of definable RV points, here integers.
  That is the hypothesis of the cited lemma, which is Lemma 8.5.2 (checked in
  the arXiv and the published versions: Delta bounded definable, l piecewise
  sum a_i x_i + b with a_i, b in Z; conclusion: rational, limit -chi(Delta)).
- A point that the proof passes over: the residue part V has a value tuple
  beta, which need not be integral. If N is the least positive integer with
  N beta integral, the coefficient of T^m is zero unless N divides m. So
  Z([U]) is not v times the series of sigma over all m. For m = N m' the
  lattice points of the piece correspond to the points of N I with
  denominator m', and the weight becomes m' l'(delta') with l' piecewise
  integral affine on N I (the constant term N c is an integer because the
  denominators of the constant terms divide N). Hence
      Z([U])(T) = v Z(N I, l')(T^N),
  and the cited lemma applies to (N I, l') in the variable T^N. chi(N I) =
  chi(I). The Hadamard product (Lemma 8.4.1 of the source) is not needed.

Depends on B02 and B03.
"""

TITLE = 'Section 8 review B08: Remark 8.10 and the proof of Theorem 8.11'
ANCHORS = ['can construct the homomorphism', 'no longer needs to go through']

EDITS = [
    (r'simply using the expression in (\ref{twist:C}) with respect to  bipolar twistoid decompositions.',
     r'bipolar twistoid decompositions.',
     r'''simply using the expression in (\ref{twist:C}) with respect to  monomial decompositions.'''),

    (r'If $[\bm U] / (\bm P_\Gamma) = \int^{\diamond}([\mdl X_f])$ then this is $Z_f(T)$.',
     r'then this is $Z_f(T)$.',
     r'''If $[\bm U] / J_{\mathrm{var}} = \int^{\diamond}([\mdl X_f])$ then this is $Z_f(T)$.'''),

    (r'Without loss of generality, we may assume that $U$ is already a bipolar twistoid and the function',
     r'$\lim_{T \limplies \infty}Z([\bm U])(T) = - \chi(I) v$.',
     r'''Both sides of the desired equality are additive. So, taking a monomial decomposition as in (\ref{hm:ass}), we may assume that $h_M(U) = V \times I^\sharp$ with $M \in \GL_n(\Z)$, $\vrv(V) = \{\beta\}$ and $I \sub \Gamma^\ell$ bounded (since $\bm U$ is doubly bounded), and that the function $l_f: U \fun \Gamma$ (Notation~\ref{comp:form}) $\vrv$-contracts to a function $\sigma : D = \vrv(U) \fun \Gamma$.  Set $v = \Theta([V]) [\G_m]^\ell$. Then, by (\ref{twist:C}),
\[
(\Theta \circ \bb E^{\diamond})([\bm U]) = \chi(I) v.
\]
On the other hand, by Lemma~\ref{muhat:section},
\[
(\bm \eta \circ \bm h_m)([\bm U]) = v \sum_{\gamma \in D_m} [\A]^{-m \sigma(\gamma)}, \qquad D_m = D \cap (m^{-1}\Z)^n.
\]
Let $N$ be the least positive integer such that $N \beta$ is a tuple in $\Z$. Since $M$ preserves the lattice $(m^{-1}\Z)^n$ and $M D = \{\beta\} \times I$, the set $D_m$ is empty unless $N$ divides $m$, and if $m = N m'$ then $\gamma \efun N \delta$, where $M \gamma = (\beta, \delta)$, is a bijection between $D_m$ and the set of the points of $N I$ in $(m'^{-1}\Z)^\ell$. The function $\sigma$ is the $\vrv$-contraction of the definable function $u \efun \rv(t)^l \prod_j f_j(u)$ on $U$. So, by Remark~\ref{GLZ:char}, it is piecewise $\Z$-affine with constant terms in $\Z$. It follows that the function $\sigma'$ on $N I$ given by $\sigma'(N \delta) = N \sigma(\gamma)$ is piecewise of the form $\delta' \efun \sum_i a_i \delta'_i + b$ with $a_i$, $b$ in $\Z$. Let
\[
Z(\sigma')(S) = \sum_{m' \in \Z^+} \sum_{\delta'} [\A]^{-m' \sigma'(\delta')} S^{m'},
\]
where $\delta'$ runs through the points of $N I$ in $(m'^{-1}\Z)^\ell$. Write $R = \gmv[[\A]^{-1}]$. By Lemma~\ref{lat:zeta}, applied to $R$ and its unit $[\A]$, the series $Z(\sigma')(S)$ is in $R[S]_{\dag}$ and $\lim_{S \limplies \infty}Z(\sigma')(S) = -\chi(N I) = - \chi(I)$. Since
\[
Z([\bm U])(T) = v Z(\sigma')(T^N),
\]
we conclude that $Z([\bm U])(T)$ belongs to $\gmv[[\A]^{-1}][T]_{\dag}$ and $\lim_{T \limplies \infty}Z([\bm U])(T) = - \chi(I) v$.'''),
]

RESOLUTIONS = {
    '154': r'The cited result is now Lemma~\ref{lat:zeta}, proved in the text. Its hypothesis is verified: the weight is the contraction of a definable $\RV$-valued function, so by Remark~\ref{GLZ:char} it is piecewise $\Z$-affine with integral constant terms. The proof also treats the case where the value $\beta$ of the residue part is not integral, by passing to $m=Nm\prime$ and to the variable $T^N$; the series is then $v$ times a series covered by that lemma, and the Hadamard product is not used.'.replace(r'm\prime', "m'"),
}
