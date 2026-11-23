"""Batch B02: the two retractions in the introduction (R007, R008).

Independent reading (Section 4).

1. Without volume forms (Section 4.1): E_b and E_g are defined on K RV[*]/(P - 1). E_b takes
   values in the degree-zero part of !K RES[*][[1]^{-1}], which is identified with !K RES
   (Remark eb:no:eg); on RES classes it is the quotient map, so it is a retraction onto !K RES.
   E_g takes values in the degree-zero part of !K RES[*][[A]^{-1}]; it needs [A] inverted and
   is not a retraction onto !K RES. By (eb:neq:eg:counter), after forgetting the grading,
   E_b([1]) = 1 and E_g([1]) = [A]^{-1}. The introduction says that both are retractions onto
   !K RES. That is false for E_g.
2. With volume forms (Proposition prop:eu:retr:k): the two maps go to !K muRES[*]/([A]), with
   volume forms and with [A] killed (the construction forces [A] = 0). The introduction says
   "onto !K RES[*]" and refers to the right column of diagram (1.2), which no longer shows
   any retraction (its bottom row is commented out in the source). The text after Remark
   res:forget explains that the quotient by [A] is what the doubly bounded categories avoid;
   the bounded retraction E^diamond of Proposition prop:eu:retr:k:db has values in !K RES.

What the batch changes: the two sentences describing the retractions. The words "is likewise a
quotient of a tensor product of" in the measured sentence belong to B01.
"""

TITLE = 'Section 1 review B02: the two retractions'
ANCHORS = ['Different targets for the two retractions', 'Measured retraction target']

EDITS = [
    (r'Anyway, we have two retractions from $\ggk \RV[*]$ onto a quotient $\sggk \RES$ of $\ggk \RES$ (the gradation is forgotten) that vanish on $(\bm P-1)$, reflecting the fact that there are two Euler characteristics in the $\Gamma$-sort; these are denoted by $\bb E_{b}$, $\bb E_{g}$.',
     r'these are denoted by $\bb E_{b}$, $\bb E_{g}$.',
     r'''Anyway, we have two homomorphisms $\bb E_{b}$, $\bb E_{g}$ on $\ggk \RV[*]$ that vanish on $(\bm P-1)$, reflecting the fact that there are two Euler characteristics in the $\Gamma$-sort, the bounded one and the geometric one (\S~\ref{subs:uni:retr:novol}). The first is a retraction onto the quotient $\sggk \RES$ of $\ggk \RES$ of Notation~\ref{res:note} (the gradation is forgotten). The second requires inverting the class $[\A]$ of the affine line and takes values in the degree-zero part of $\sggk \RES[*][[\A]^{-1}]$; for instance, after forgetting the gradation, $\bb E_{b}([1]) = 1$ whereas $\bb E_{g}([1]) = [\A]^{-1}$ (Remark~\ref{eb:no:eg}).'''),
    (r'$\ggk \mgRES[*]$ and $\ggk \mG[*]$, which induces two retractions $\mgE_ {b}$, $\mgE_{g}$ from $\ggk\mgRV[*]$ onto $\sggk \RES[*]$ that vanish on $(\bm P)$; see the right column of the diagram (\ref{diag-diamond-interpol}).',
     r'see the right column of the diagram (\ref{diag-diamond-interpol}).',
     r'''$\ggk \mgRES[*]$ and $\ggk \mG[*]$, which induces two graded homomorphisms $\mgE_ {b}$, $\mgE_{g}$ from $\ggk\mgRV[*]$ to $\sggk \mgRES[*]/([\A])$ that vanish on $(\bm P)$ and restrict to the quotient map on $\ggk \mgRES[*]$ (Proposition~\ref{prop:eu:retr:k}). The construction forces $[\A] = 0$, which is detrimental to our purpose; this is avoided by the doubly bounded categories below.'''),
]

RESOLUTIONS = {
    '007': r'The two homomorphisms are now described separately: $\bb E_b$ is a retraction onto $\sggk \RES$, while $\bb E_g$ requires inverting $[\A]$ and takes values in the degree-zero part of $\sggk\RES[*][[\A]^{-1}]$. The example $\bb E_b([1]) = 1$, $\bb E_g([1]) = [\A]^{-1}$ of Remark~\ref{eb:no:eg} is quoted.',
    '008': r'The target is now $\sggk\mgRES[*]/([\A])$, as in Proposition~\ref{prop:eu:retr:k}, and the sentence says that the doubly bounded categories avoid the quotient by $[\A]$. The reference to a column of diagram~\eqref{diag-diamond-interpol}, which no longer shows the retractions, is removed.',
}
