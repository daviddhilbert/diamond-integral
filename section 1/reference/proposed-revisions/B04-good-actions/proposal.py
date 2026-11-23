"""Batch B04: good actions and the ring K^muhat Var_C (R011); the sentence on Theta.

Independent reading. Notation bipo:gdv (Section 5, approved earlier) defines the ring as follows:
K^{muhat,raw} Var_C has good finite muhat-actions (the action factors through some mu_N and
every orbit lies in an affine open subset) and equivariant scissor relations; K^muhat Var_C is
its quotient by [X x (A^r, rho)] - [X x A^r] for every good equivariant X and every finite linear
action rho, with the trivial action on the second affine factor. It says explicitly that
goodness and this relation are separate conditions. The introduction folds the relation into the
word "good" and states it only for vector spaces, without the factor X. This is the definition of
Denef-Loeser, Geometry on arc spaces, Section 2.4 (reference [denefloeser:arc]).

The same Notation constructs the isomorphism Theta : !K RES -> K^muhat Var_C at a finite Kummer
level and proves both directions. The introduction says "whose finite-level Kummer construction
is proved in Notation ...", a phrase from the formalization records; it is replaced by a plain
reference.
"""

TITLE = 'Section 1 review B04: good actions'
ANCHORS = ['Good actions and the', 'which is constructed in Notation']
SELECT = True

EDITS = [
    (r'Let $\ggk \var_{\C}$ be the Grothendieck ring of complex algebraic varieties and $\ggk^{\hat \mu} \var_{\C}$ the corresponding Grothendieck ring with good $\hat \mu$-actions.',
     r'endowed with the trivial $\hat \mu$-action.',
     r'''Let $\ggk \var_{\C}$ be the Grothendieck ring of complex algebraic varieties. An action of $\hat \mu$ on a variety is \memph{good} if it factors through some $\mu_n$ and every orbit is contained in an affine open subset. Let $\ggk^{\hat \mu} \var_{\C}$ be the Grothendieck ring of varieties with good $\hat \mu$-actions modulo the additional relation $[X \times (\A^r, \rho)] = [X \times \A^r]$, for every variety $X$ with a good $\hat \mu$-action and every linear action $\rho$ of some $\mu_n$ on $\A^r$, where the action on the factor $\A^r$ on the right is trivial (see Notation~\ref{bipo:gdv} and \cite[\S~2.4]{denefloeser:arc}).'''),
    (r'whose finite-level Kummer construction is proved in Notation~\ref{bipo:gdv}.',
     r'whose finite-level Kummer construction is proved in Notation~\ref{bipo:gdv}.',
     r'''which is constructed in Notation~\ref{bipo:gdv}.'''),
]

RESOLUTIONS = {
    '011': r'Goodness (factorization through some $\mu_n$ and orbits in affine open subsets) and the additional relation $[X \times (\A^r,\rho)] = [X \times \A^r]$, with an arbitrary equivariant factor $X$, are now stated separately, as in Notation~\ref{bipo:gdv} and Denef--Loeser, Section~2.4.',
}
