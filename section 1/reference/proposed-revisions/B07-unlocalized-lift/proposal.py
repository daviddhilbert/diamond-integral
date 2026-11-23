"""Batch B07: the class before and after localization (R016).

Independent reading. S_f is defined in R = K^muhat Var_C[[A]^{-1}] as -lim Z_f (Section 8.2). The
class (Theta o E_b o integral)([X_f]) is defined in K^muhat Var_C without inverting [A]; it equals
(Theta o E^diamond o integral^diamond)([X_f]) (Corollary db:to:novol and (edb:eb:com)), whose image in
R is S_f by Theorem direct:mil. Remark rem-comp-milnor-fib shows that the map
K^muhat Var_C -> R is not injective (Borisov), so the unlocalized class is not determined by S_f:
it is a canonical lift of S_f. The introduction says "we can recover S_f directly ... in
K^muhat Var_C", which identifies the two. Remark rem-comp-milnor-fib itself adopts the other point
of view explicitly ("we can forego the zeta function point of view"), so it needs no change.

The same identification occurs two paragraphs later: "Vol(F^an_f). This is indeed the motivic
Milnor fiber S_f." Vol takes values in the unlocalized ring. Remark rem-comp-milnor-fib-bis proves
Vol([X_f]) = Vol([X_t]), where X_t contains the Puiseux points of the analytic Milnor fiber, so
Vol(F^an_f) is the same canonical lift, and its image after inverting [A] is S_f.
"""

TITLE = 'Section 1 review B07: the unlocalized class'
ANCHORS = ['also lives in', 'Class before and after localization', 'is the same canonical lift']

EDITS = [
    (r'Since $\mdl X_f$ also lives in $\VF_*$, we can recover   $\mathscr S_{f}$ directly as $(\Theta \circ \bb E_b \circ \int)([\mdl X_f])$ in $\gmv$, without even inverting $[\A]$. This is indeed a salient point.',
     r'This is indeed a salient point.',
     r'''Since $\mdl X_f$ also lives in $\VF_*$, the class $(\Theta \circ \bb E_b \circ \int)([\mdl X_f])$ is defined in $\gmv$, without even inverting $[\A]$, and its image in $\gmv[[\A]^{-1}]$ is $\mathscr S_{f}$ (Theorem~\ref{direct:mil} and Remark~\ref{rem-comp-milnor-fib}). This is indeed a salient point: it is a canonical lift of $\mathscr S_{f}$ to $\gmv$. The lift is not determined by $\mathscr S_f$ alone, since the natural homomorphism $\gmv \fun \gmv[[\A]^{-1}]$ is not injective (Remark~\ref{rem-comp-milnor-fib}).'''),
    (r'This is indeed the motivic Milnor fiber $\mathscr S_{f}$. This fact is already proven',
     r'This is indeed the motivic Milnor fiber $\mathscr S_{f}$.',
     r'''By Remark~\ref{rem-comp-milnor-fib-bis}, $\Vol(\mathcal{F}^{\mathrm{an}}_{f}) = \Vol([\mdl X_f])$; this is the same canonical lift, so its image in $\gmv[[\A]^{-1}]$ is the motivic Milnor fiber $\mathscr S_{f}$.''', True),
]

RESOLUTIONS = {
    '016': r'The sentence now says that $(\Theta \circ \bb E_b \circ \int)([\mdl X_f])$ is a class in the unlocalized ring whose image after inverting $[\A]$ is $\mathscr S_f$, a canonical lift of $\mathscr S_f$, and that it is not determined by $\mathscr S_f$ because the localization map is not injective (Remark~\ref{rem-comp-milnor-fib}). The sentence on the analytic Milnor fiber now says that its volume is the same lift (Remark~\ref{rem-comp-milnor-fib-bis}).',
}
