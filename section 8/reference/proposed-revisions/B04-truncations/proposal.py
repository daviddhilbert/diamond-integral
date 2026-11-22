"""Batch B04: truncations A[m; beta] and the relation of Hrushovski-Loeser Lemma 4.2.1 (R143, R144).

Independent reading.
- The coefficient space C[t^{1/m}]/t^{beta_i + 1/m} is described as the product of
  the sets gamma^sharp, 0 <= gamma <= beta_i. With the manuscript's convention
  gamma^sharp = vrv^{-1}(gamma) has no zero, and the index must run over the
  lattice. The revised Section 5 already has the residue line
  L_gamma = gamma^sharp u {0_gamma} (proof of Notation 5.14); it is used here.
  RES_m must then allow the coordinate infinity.
- The relation [A[m; beta']] = [A[m; beta]] [A]^{m Sigma(beta' - beta)} is false
  in K RES_m: for A = O, m = 2, beta = 0, beta' = 1/2 the two sides are L_0 x L_{1/2}
  and L_0 x L_0, and mu_2 acts on L_{1/2} by the sign; the fixed loci have
  classes [A] and [A]^2. It holds in !K RES, where [L_gamma] = [G_m] + 1 = [A].
  Checked in the source (arXiv:1111.1954v2 and the published version): the
  cited lemma is stated in K(RES_{m^{-1}Z}) and its proof ends with
  "X[m; beta'] = X[m; beta] x A^1", which ignores the action on the line.
- The relation has a one-line proof: A is beta-invariant, so the coefficients
  of t^gamma with beta_i < gamma <= beta'_i are unrestricted and A[m; beta'] is
  literally A[m; beta] times a product of lines L_gamma.
- A sentence is added on maps induced on truncations; it is used in the proof
  of Lemma 8.6 (batch B05) and is what Hrushovski-Loeser use after their
  Lemma 4.2.1.
"""

TITLE = 'Section 8 review B04: truncations and the relation of Lemma 8.5'
ANCHORS = ['Denote by RES', 'Lemma 8.6.']

EDITS = [
    (r'Denote by $\RES_{m}$ the full subcategory of $\RES$ such that',
     r'(see \cite[\S~4.2]{hru:loe:lef} for more details).',
     r'''Denote by $\RES_{m}$ the full subcategory of $\RES$ such that $U \in \RES_{m}$ if and only if every coordinate of every element of $U$ is either $\infty$ or has value in $m^{-1} \Z$, or equivalently, $U \in \RES_{m}$ if and only if the action on $U$ of the kernel of the canonical projection $\hat \mu \fun \mu_m$ is trivial.

For $\gamma \in \Q$, let $L_\gamma = \gamma^\sharp \cup \{0_\gamma\}$ be the one-dimensional residue vector space introduced in the proof of Notation~\ref{bipo:gdv}. Its class in $\sggk \RES$ is $[\G_m] + 1 = [\A]$.

Let $\beta = (\beta_1, \ldots, \beta_n) \in (m^{-1} \Z)^n$ with $\beta_i \geq 0$ and $A \sub \OO^n \times \RV^l$ be a proper $\beta$-invariant definable set such that $\pvf \rest A$ is finite-to-one. Then there is a set
\[
A[m;\beta] \sub \prod_i \C[t^{1/m}] / t^{\beta_i + 1/m} \times \RV(\C \dpar{t^{1/m}})^l
\]
such that, for every $t \in \RV(\C \dpar{t^{1/m}})^l$, the $\VF$-fiber $A_t(\C \dpar{t^{1/m}})$ is, under the obvious quotient map, the preimage of the fiber $A[m;\beta]_t$. Note that $\pvf \rest A[m;\beta]$ is still finite-to-one, for otherwise, by the $\beta$-invariance of $A$, $\pvf \rest A$ would fail to be finite-to-one. We can think of $\C[t^{1/m}] / t^{\beta_i + 1/m}$ as the object $\prod_{\gamma} L_\gamma$ of $\RES_{m}$, where $\gamma$ runs through the elements of $m^{-1}\Z$ with $0 \leq \gamma \leq \beta_i$ and the coefficient of $t^\gamma$ is regarded as an element of $L_\gamma$. Then, since every element in the value group $\Q$ is definable and the values of the $\RV$-coordinates of $A[m;\beta]$ are doubly bounded,  it follows that  $A[m;\beta]$ is indeed a finite disjoint union of definable sets in $\RV_\infty$ (no extra parameters other than those in $\mathbb{S} = \C \dpar{ t }$ are needed) and hence, as such, is an object of $\RES_{m}$ (see \cite[\S~4.2]{hru:loe:lef} for more details). The same applies to graphs: if $B \sub \OO^n \times \RV^{l'}$ is a proper $\beta$-invariant definable set and $F : A \fun B$ is a definable bijection that induces a bijection between $A[m;\beta]$ and $B[m;\beta]$, then the induced bijection is definable, and hence $[A[m;\beta]] = [B[m;\beta]]$ in $\ggk \RES_m$.'''),

    (r'''\begin{lem}[{\cite[Lemma~4.2.1]{hru:loe:lef}}]
Let $\beta' \in (m^{-1} \Z)^n$''',
     r'''\in \ggk \RES_{m}.
\end{equation}
\end{lem}''',
     r'''\begin{lem}[{\cite[Lemma~4.2.1]{hru:loe:lef}}]
Let $\beta' \in (m^{-1} \Z)^n$ with $\beta_i \leq \beta'_i$ for all $i$. Then
\begin{equation}\label{arc:com}
  [A[m;\beta']] = [A[m;\beta]][\A]^{m \Sigma (\beta' - \beta)} \in \sggk \RES.
\end{equation}
\end{lem}
\begin{proof}
Since $A$ is $\beta$-invariant, a point of $A$ that is rational over $\C \dpar{t^{1/m}}$ remains in $A$ when the coefficients of $t^\gamma$ in its $i$th $\VF$-coordinate, $\gamma > \beta_i$, are changed. So
\[
A[m;\beta'] = A[m;\beta] \times \prod_i \prod_{\gamma} L_\gamma,
\]
where, for each $i$, $\gamma$ runs through the $m(\beta'_i - \beta_i)$ elements of $m^{-1}\Z$ with $\beta_i < \gamma \leq \beta'_i$. The equality follows since $[L_\gamma] = [\A]$ in $\sggk \RES$.
\end{proof}
The equality (\ref{arc:com}) does not hold in $\ggk \RES_{m}$ in general, because $L_\gamma$ is not isomorphic to $L_0$ unless $\gamma \in \Z$: under $\Theta$ it becomes an affine line on which $\mu_m$ acts through the character $\zeta \efun \zeta^{m\gamma}$.'''),

    (r'Thus the element $[A[m;\beta]][\A]^{- m\sum \beta }$ in $\ggk \RES_{m}[[\A]^{-1}]$ does not depend on $\beta$; we denote it by $\tilde A[m]$.',
     r'we denote it by $\tilde A[m]$.',
     r'''Thus the element $[A[m;\beta]][\A]^{- m\sum \beta }$ in $\sggk \RES[[\A]^{-1}]$ does not depend on $\beta$; we denote it by $\tilde A[m]$.'''),
]

RESOLUTIONS = {
    '143': r'The coefficient space is now the product of the residue lines $L_\gamma=\gamma^\sharp\cup\{0_\gamma\}$ of Notation~\ref{bipo:gdv} over the lattice indices $0\leq\gamma\leq\beta_i$, with $\beta_i\geq0$, and $\RES_m$ allows the coordinate $\infty$.',
    '144': r'The relation \eqref{arc:com} is now stated in $\sggk\RES$, with a proof: by invariance $A[m;\beta\prime]$ is the product of $A[m;\beta]$ and residue lines $L_\gamma$, and $[L_\gamma]=[\A]$ in $\sggk\RES$. A sentence records that it fails in $\ggk\RES_m$. The element $\tilde A[m]$ is taken in $\sggk\RES[[\A]^{-1}]$.'.replace(r'\beta\prime', r"\beta'"),
}
