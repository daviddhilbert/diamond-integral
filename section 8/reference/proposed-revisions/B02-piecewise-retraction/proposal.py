"""Batch B02: the assignment h_m and Lemma 8.2 in the language of the revised Section 5
(R139, R140, R141; the two undefined references bipo:desc and shift:K:csn:def).

Independent reading. After the approved Section 5 rewrite there is no
cross-section, no "bipolar twistoid decomposition", no twistback and no
"Gamma-cohesive" decomposition; Lemma 5.12 gives monomial decompositions
h_{M_i}(U_i) = V_i x I_i^sharp, and Remark 4.14 (tensor:bd) only states that
mu Psi^db is a homomorphism. So (hm:ass), the product formula after it, the
sentence about mu Psi^db, and the proof of Lemma 8.2 (which rests on cohesive
refinements and on a lemma that no longer exists) have to be restated.

The formula (hm:ass) is kept, with Theta([V_i])[G_m]^{l_i} in place of the
twistback class. Lemma 8.2 now states the identity
    h_m(U) = sum_w Theta([U^(m)_w]) T^{-mw},
where U^(m)_w is the set of points of U with value in the lattice and weight
w. The right-hand side involves no choice, which gives independence of the
decomposition; invariance under isomorphism follows from omega_f = pi_g o F
(the Gamma-Jacobian condition) and functional closure of C((t^{1/m})).

Checks made: the sign of the Gamma-Jacobian (Notation 2.2 and (cond:mg2))
gives omega_f = pi_g o F; GL_n(Z) preserves (m^{-1}Z)^n; a fibre of a
monomial piece over a lattice value is V_i x delta^sharp, of class
Theta([V_i])[G_m]^{l_i} by the relation [q^sharp] = [G_m] of !K RES; the
pieces on which omega_f contracts exist because the number of values of
omega_f on U_gamma is bounded uniformly in gamma.
"""

TITLE = 'Section 8 review B02: the piecewise retraction h_m and Lemma 8.2'
ANCHORS = ['Notation 8.1.', 'Lemma 8.3.']

EDITS = [
    (r'Recall Notations~\ref{comp:form} and \ref{bipo:gdv}. Let $\bm U = (U, f, \omega) \in \mgRV^{\db}[k]$.',
     r'Computationally, though,  (\ref{hm:ass}) is more effective.',
     r'''Recall Notation~\ref{comp:form}, Lemma~\ref{coh:decom} and the isomorphism $\Theta$ of Notation~\ref{bipo:gdv}. Let $\bm U = (U, f, \omega) \in \mgRV^{\db}[k]$, where $U \sub \RV^n$. In particular, if $f=(f_1,\dots,f_k)$, we have introduced the shorthand
\[
\omega_{f}: x\in U \efun \omega(x)+\sum_{i=1}^k\vrv(f_i(x)).
\]
For $\gamma \in \vrv(U)$ write $U_\gamma = U \cap \vrv^{-1}(\gamma)$. The image $\omega_f(U_\gamma)$ is finite for every $\gamma \in \vrv(U)$, because the $\K$-sort and the $\Gamma$-sort are orthogonal to each other. Its size is bounded uniformly in $\gamma$, so, listing the values of $\omega_f$ on $U_\gamma$ in increasing order, we get a finite definable partition of $U$ on each piece of which $\omega_f$ $\vrv$-contracts to a function. Applying Lemma~\ref{coh:decom} to each piece, it follows that there is a monomial decomposition $(U_i)_i$ of $U$, with
\[
h_{M_i}(U_i) = V_i \times I_i^\sharp, \qquad \vrv(V_i) = \{\beta_i\}, \qquad I_i \sub \Gamma^{\ell_i},
\]
such that each restriction $\omega_f \rest U_i$ $\vrv$-contracts to a function $\sigma_i : D_i = \vrv(U_i) \fun \Gamma$. Write $D_{i,m}$ for the set $D_i \cap (m^{-1}\Z)^n$ of  $m^{-1}\Z$-rational points of $D_i$; it is finite because $D_i$ is doubly bounded. We assign to $\bm U$ the expression
\begin{equation}\label{hm:ass}
  h_m(\bm U) = \sum_i \Theta([V_i]) [\G_m]^{\ell_i} \sum_{\gamma \in D_{i,m}} T^{-m \sigma_i(\gamma)},
\end{equation}
which is  a finite sum and hence  belongs to $\gmv[[\A]^{-1}][T^{\Q}]$. Note that $M_i \in \GL_n(\Z)$ preserves the lattice $(m^{-1}\Z)^n$, and hence $D_{i,m}$ is empty unless $\beta_i$ is a tuple in $m^{-1}\Z$.

If $\bm U$ is already of the form $(V, g, \omega') \times (I, \sigma) \in \mgRES[i] \times \mG^{\db}[j]$, where $\vrv(V)$ is a singleton $\{\delta\}$ and $\omega'_g$ is constant, then clearly
\[
h_m(\bm U) = \Theta([V])T^{-m\omega'_g} \cdot [\G_m]^{j} \sum_{\gamma \in I_{m}} T^{-m (\sigma(\gamma) + \Sigma \gamma )}
\]
if $\delta$ is a tuple in $m^{-1}\Z$, where $I_m = I \cap (m^{-1}\Z)^j$, and $h_m(\bm U) = 0$ otherwise. Every object of $\mgRES[i]$ is a finite disjoint union of such objects $(V, g, \omega')$. On the image of the homomorphism ${\mu} \Psi^{\db}$ in Remark~\ref{tensor:bd}, this is essentially how the assignment is given in \cite[\S~8.2]{hru:loe:lef}. We do not take it as the definition of $h_m$, since that would require its compatibility with the relations among the tensor classes. Computationally, too,  (\ref{hm:ass}) is more effective.'''),

    (r"The ``piecewise retraction'' formula (\ref{hm:ass}) is indeed quite similar",
     r'which depends on $E$, are  equal.',
     r'''The ``piecewise retraction'' formula (\ref{hm:ass}) is indeed quite similar to the ``uniform retraction'' formula (\ref{twist:C}). The difference is just that the coefficient $\chi_b(I_i)$ in the latter is replaced in the former by a formal ``counting'' sum $\sum_{\gamma \in D_{i,m}} T^{-m \sigma_i(\gamma)}$ that also takes the volume form into account. As noted after (\ref{twist:C}), that the ``uniform retraction'' formula does not depend on the choice of the monomial decomposition is simply a consequence of the construction of $\bb E_b$ itself. The same holds for the ``piecewise retraction'' formula, but we do need an argument.

For $w \in \Gamma$, write
\[
U^{(m)}_w = \set{u \in U \given \vrv(u) \in (m^{-1}\Z)^n \text{ and } \omega_f(u) = w}.
\]
Since $\vrv(U)$ is doubly bounded, the set $\vrv(U) \cap (m^{-1}\Z)^n$ is finite, and each of its points is definable. Hence $U^{(m)}_w$ is a definable set with finite value support, that is, an object of $\RES$, and it is nonempty for only finitely many $w$.

\begin{lem}\label{muhat:section}
For every $\bm U = (U, f, \omega) \in \mgRV^{\db}[k]$,
\[
h_m(\bm U) = \sum_{w} \Theta([U^{(m)}_w])\, T^{-mw}.
\]
In particular, the  assignment (\ref{hm:ass}) does not depend on the choice of the monomial decomposition and is invariant on isomorphism classes.
\end{lem}
\begin{proof}
Let $(U_i)_i$ be a monomial decomposition as above. For $\gamma \in D_{i,m}$, write $M_i \gamma = (\beta_i, \delta)$. Then $h_{M_i}$ restricts to a definable bijection between $U_i \cap \vrv^{-1}(\gamma)$ and $V_i \times \delta^\sharp$, and $\Theta([\delta^\sharp]) = [\G_m]^{\ell_i}$ by the defining relations of $\sggk \RES$. Since $\omega_f$ is constant on $U_i \cap \vrv^{-1}(\gamma)$, with value $\sigma_i(\gamma)$, the set $U^{(m)}_w$ is the disjoint union of the sets $U_i \cap \vrv^{-1}(\gamma)$ with $\gamma \in D_{i,m}$ and $\sigma_i(\gamma) = w$, each of which has class $\Theta([V_i]) [\G_m]^{\ell_i}$ under $\Theta$. Summing over $w$ gives the displayed equality. Its right-hand side does not involve the decomposition.

Let $\bm V = (V, g, \pi) \in \mgRV^{\db}[k]$, where $V \sub \RV^{n'}$, and let $F : \bm U \fun \bm V$ be a $\mgRV^{\db}[k]$-morphism. We need to show that $h_m(\bm U)$ and $h_m(\bm V)$ are  equal.''', 'switch'),

    (r'This is clear if $\bm U = \bm V$,  and $E$ is trivial',
     'The result follows.\n\\end{proof}',
     r'''By (\ref{cond:mg2}) and Notation~\ref{jcbG:op}, $\omega_f = \pi_g \circ F$. So it is enough to show that, for every $u \in U$, $\vrv(u)$ is a tuple in $m^{-1}\Z$ if and only if $\vrv(F(u))$ is. Both conditions define subsets of $U$ over $\mathbb{S}$, so this may be checked for the points of $U$ in $\puC$. The residue fields of $\puC$ and of $\C \dpar{ t^{1/m} }$ are both $\C$, and hence an element of $\RV(\puC)$ lies in $\RV(\C \dpar{ t^{1/m} })$ if and only if its value is in $m^{-1}\Z$. The claim follows because $\C \dpar{ t^{1/m} }$ is functionally closed and $F$, $F^{-1}$ are definable. Therefore $F$ restricts to a definable bijection between $U^{(m)}_w$ and $V^{(m)}_w$ for every $w$, and these two objects of $\RES$ have the same image under $\Theta$.
\end{proof}''', 'switch'),

    (r'Thus, $h_m$ may be viewed as a map on $\gsk \mgRV^{\db}[k]$. It is now routine to check that  we have in effect constructed a ring homomorphism',
     r'we have in effect constructed a ring homomorphism',
     r'''Thus, $h_m$ may be viewed as a map on $\gsk \mgRV^{\db}[k]$. It is additive, since $(U \uplus U')^{(m)}_w = U^{(m)}_w \uplus U'^{(m)}_w$, and multiplicative, since the weight of a product is the sum of the weights, so that $(U \times U')^{(m)}_w$ is the disjoint union of the sets $U^{(m)}_{w_1} \times U'^{(m)}_{w_2}$ with $w_1 + w_2 = w$. So we have in effect constructed a ring homomorphism'''),
]

RESOLUTIONS = {
    '139': r'The $\RES$ factor is now assumed to have a single value tuple $\delta$; the formula is stated for $\delta$ a tuple in $m^{-1}\Z$ and the value is $0$ otherwise. Every object of $\mgRES[i]$ is a finite disjoint union of such pieces.',
    '140': r'The isomorphism is now called $F$; the letter $f$ is kept for the structural map.',
    '141': r'The proof of Lemma~\ref{muhat:section} now states both points: $\omega_f=\pi_g\circ F$ by the $\Gamma$-Jacobian condition, and $F$ preserves the points whose values lie in the lattice because $\C\dpar{t^{1/m}}$ is functionally closed. Then $F$ restricts to definable bijections $U^{(m)}_w\fun V^{(m)}_w$ of objects of $\RES$, whose classes agree under $\Theta$.',
}
