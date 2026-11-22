"""Batch B07: the nonarchimedean Milnor fiber as an object, and the coefficient comparison
(R150, R152, R153).

Independent reading.
- "Suppose that 0 in X(C) cap f^{-1}(0) is singular": X is smooth, so the word can
  only refer to f. Nothing in the section uses that 0 is a critical point
  (Hrushovski-Loeser take any closed point of f^{-1}(0)). The hypothesis is
  restated as f(0) = 0, with the critical case named as the one of interest.
- "X_f may be constructed in an affine neighborhood of 0 and hence is a
  definable set ... beta-invariant for every beta >= 1 ... an object of
  mu VF^diamond[*]". An affine embedding in A^N with N > d gives a set that
  is not open in VF^N, so it is not proper invariant, and X(M) has no literal
  meaning. With an etale chart q at 0, Hensel's lemma identifies the points of
  X(O) that reduce to 0 with M^d, and X_f becomes a subset of M^d. Invariance
  for beta >= 1: the function is given in the chart by a power series over C
  with integral coefficients on M^d, so x' - x in M_1^d implies
  f(x') - f(x) in M_1, and val f(x) = 1.
  Independence of the chart in K mu VF^diamond[d] is true (the transition is
  a composition of relatively unary proper covariant homeomorphisms with
  Jacobian of value 0; see SECTION7-HANDOFF, item B4) but it is not needed:
  the coefficients are identified with the classes of the jet spaces, which
  do not involve the chart. The text fixes a chart and says so.
- The second equality of (z:coeff:change): with s = t^{1/m} and
  beta = (1, ..., 1), the truncation is modulo s^{m+1}, the condition
  rv(f(x)) = rv(t) reads f(x) = s^m mod s^{m+1}, and the chart identifies the
  jets at 0 with (s C[s]/s^{m+1})^d. So X_f[m; beta] is the jet space (with the
  base point condition added in the routine corrections), mu_m acts by
  s -> zeta s, and the normalization is [A]^{-md}. These sentences are added.

Depends on B05 (Lemma 8.6 with A inside O^n).
"""

TITLE = 'Section 8 review B07: the nonarchimedean Milnor fiber as an object of the category'
ANCHORS = ['Finally, we proceed to replicate', 'which is understood as the']

EDITS = [
    (r'Suppose that $0 \in X(\C) \cap f^{-1}(0)$ is singular.',
     r'is singular.',
     r'''Let $0$ denote a point of $X(\C)$ with $f(0) = 0$; the case of interest is that of a critical point of $f$.'''),

    (r'Note that $\mdl X_f$ may be constructed in an affine neighborhood of $0$ and hence is indeed a (quantifier-free) definable set.',
     r'equipped with the constant volume form $0$.',
     r'''Here $X(\MM)$ stands for the set of the points of $X(\OO)$ that specialize to $0$. To regard $\mdl X_f$ as a definable set, choose an \'etale map $q$ from a neighborhood of $0$ in $X$ to $\A^d$ with $q(0) = 0$. By Hensel's lemma, $q$ induces a bijection between $X(\MM)$ and $\MM^d$, and we identify $\mdl X_f$ with its image in $\MM^d$. In these coordinates $f$ is given on $\MM^d$ by a power series with coefficients in $\C$ and no constant term, so that $f(x') - f(x) \in \MM_1$ whenever $x' - x \in \MM_1^d$. Since $\vv(f(x)) = 1$ for $x \in \mdl X_f$, it follows that $\mdl X_f$ is a (quantifier-free) definable subset of $\MM^d$ that is $\beta$-invariant for every $\beta \geq 1$. Therefore, $\mdl X_f$ may be regarded as an object of $\mgVF^\diamond[d]$ equipped with the constant volume form $0$. The chart $q$ is fixed; the coefficients computed in (\ref{z:coeff:change}) below do not depend on it.'''),

    (r'where the second equality follows if  we change the variable $t$ to $t^{1/m}$ in (\ref{f:m:arc})',
     r'which is how they are usually defined.',
     r'''where the second equality follows if  we change the variable $t$ to $t^{1/m}$ in (\ref{f:m:arc}) (see the discussion in \cite[\S~6.2]{hru:loe:lef} for  detail). More precisely, put $s = t^{1/m}$ and take $\beta = (1, \ldots, 1)$. The truncation $\mdl X_f[m;\beta]$ is taken modulo $s^{m+1}$, and for a point $x$ of $\mdl X_f$ that is rational over $\C \dpar{s}$ the condition $\rv(f(x)) = \rv(t)$ reads $f(x) = s^m \mod s^{m+1}$. The chart $q$ identifies the truncated arcs $\varphi \in X(\C[s]/(s^{m+1}))$ with $\varphi(0) = 0$ with the elements of $(s\C[s]/(s^{m+1}))^d$. Hence $\mdl X_f[m;\beta]$ is $\mdl X_m$, written in the variable $s$, the action of $\mu_m$ through $s \efun \zeta s$ is the usual one on truncated arcs, and the normalizing factor is $[\A]^{-m \Sigma \beta} = [\A]^{-md}$. This shows that the coefficients of $Z_f(T)$ may also be written as $[\mdl X_{m}][\A]^{-md}$, which is how they are usually defined.'''),
]

RESOLUTIONS = {
    '150': r'The hypothesis now reads: $0$ is a point of $X(\C)$ with $f(0)=0$, the case of interest being a critical point of $f$. Nothing below uses that the point is critical.',
    '152': r'The notation $X(\MM)$ is explained, and $\mdl X_f$ is identified with a subset of $\MM^d$ through a fixed \'etale chart at $0$; invariance for $\beta\geq1$ is proved in these coordinates. The class of $\mdl X_f$ is used only through the coefficients in \eqref{z:coeff:change}, which do not depend on the chart, so no comparison of charts is needed.',
    '153': r'The comparison is now written out: $s=t^{1/m}$, $\beta=(1,\ldots,1)$, truncation modulo $s^{m+1}$, the identification of the truncated arcs at $0$ through the chart, the action of $\mu_m$, and the factor $[\A]^{-md}$.',
}
