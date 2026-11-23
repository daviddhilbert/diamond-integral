"""Batch B09: Section 5 becomes a short section citing the Fubini paper; the outline of the paper.

Author's decision (November 22): the Fubini theorems are in their own paper (Forey-Yin, "Fubini
theorems for motivic volume", in the Fubini repository); Section 5 is replaced by a short section
that recalls what this paper uses, so that Sections 6-8 keep their numbers.

Verification (against the Fubini paper on origin/main, commit d8552cc, 19 November):
- Lemma coh:decom (monomial decomposition) = Fubini paper Lemma 2.1, same statement; its proof
  there uses a Smith-normal-form basis.
- Notation bipo:gdv (good actions, the extra relation, the lines L_q, the isomorphism Theta and
  its finite Kummer construction) = Fubini paper Notation 7.3, with Remarks 7.1 (ambient model)
  and 7.2 (Kummer actions); formula (twist:C) = its (7.1); Notation mov:vol = its Notation 7.4.
- The Fubini theorem, its geometric version, the inflated-family theorem and the vanishing
  corollary are its Theorem 3.2, Proposition 4.2, Theorem 6.1, Corollary 7.6.
- The Fubini paper cites this paper only for the retractions of Section 4, which do not use
  Section 5, so the mutual citation is not circular.
Numbers in the Fubini paper were read from its source (the offline TeX cache cannot build it).

Uses of Section 5 elsewhere in this paper: Lemma coh:decom (formula (hm:ass), Theorem direct:mil,
the remark before it), Notation bipo:gdv (introduction; Section 8: Theta, and the lines L_gamma
"introduced in the proof of" it), (twist:C) (Section 8), Notation mov:vol (Remarks
rem-comp-milnor-fib and Corollary db:to:novol context), and the opening of Section 8 ("As in
Section 5.1"). All labels used elsewhere are kept. The Section 8 sentence on L_gamma now points
to the Notation itself, and the opening of Section 8 no longer refers to the deleted subsection.
The referee text of R019 cited Theorem fubini and Remark rem:volb, which are deleted; those two
references are written out with their former numbers.

Removed with the text of Section 5: the referee items R080-R095 (all resolved), the author
resolution notes THETA and "geometric Fubini", the opening sentences about the Fubini statements
and the language, the Kummer-action remark, the proofs, Section 5.1 (tropical Fubini) and Section
5.2 (Fubini theorem). The bibliography gains the Fubini paper; [loeser2019motivic] is no longer
cited (its only citation was removed in B08) and is deleted.

The outline at the end of the introduction (no referee item; R020 was routine) omitted Section 5
and said that Section 6 establishes "the surjectivity of the lifting homomorphism (1.1)"; (1.1) is
L : K RV[*] -> K VF_*, whose surjectivity is cited from Hrushovski-Kazhdan in Section 3. Section 6
proves the surjectivity of the lifting from K muRV^db[*] to K muVF^diamond[*] (Corollary L:sur:c).
The outline now describes Section 5 and cites Corollary L:sur:c.

Numbering: \\setcounter keeps Lemma 5.12 (as before), Notation 5.14 and Notation 5.15; nothing in
Sections 6-8 is renumbered.
"""

TITLE = 'Section 1 review B09: Section 5 and the outline'
ANCHORS = ['The paper is organized as follows', 'Monomial decomposition', 'motivic volume operator is',
           'Special covariant bijections', 'From here on, we work in the field', 'be the one-dimensional residue vector space of',
           'Fubini theorems for motivic volume, manuscript']
SELECT = True

_src = (__import__('pathlib').Path(__file__).resolve().parents[4] / 'section 2/reference/diamond_integral_revision_annotated.tex').read_text()
_start = r'\section{Interlude: RV decomposition and Fubini theorems}\label{csndag}'
_end_anchor = r'% END APPROVED GEOMETRIC FUBINI'

NEW_SECTION = r'''\section{Interlude: RV decomposition and the realization in varieties}\label{csndag}
\ReviewOnly{The former Section 5 (monomial decomposition with proof, Section 5.1 on the tropical motivic Fubini theorem, Section 5.2 on the Fubini theorem, with referee items R080 to R095) is replaced by the text below.}
The results recalled in this section are proved in \cite{FY:Fubini}, together with Fubini theorems for the motivic volume that are not used in this paper. They are used in Section~\ref{sec:spec:pui}.

For an integer matrix $M=(m_{ab})\in\GL_n(\Z)$, write
\[
 h_M:(\RV^\times)^n\longrightarrow(\RV^\times)^n,\qquad
 (h_M(u))_a=\prod_b u_b^{m_{ab}}.
\]
Thus $h_M^{-1}=h_{M^{-1}}$ and $\vrv(h_M(u))=M\vrv(u)$. For $I\subseteq\Gamma^\ell$, the notation $I^\sharp$ means its full inverse image in $(\RV^\times)^\ell$ under $\vrv$.

\setcounter{thm}{11}
\begin{lem}[Monomial decomposition {\cite[Lemma~2.1]{FY:Fubini}}]\label{coh:decom}
Let $U\subseteq(\RV^\times)^n$ be definable. There is a finite definable partition $(D_i)_i$ of $\vrv(U)$ such that, writing $U_i=U\cap\vrv^{-1}(D_i)$, there are $M_i\in\GL_n(\Z)$, $0\leq m_i\leq n$, a nonempty definable set $V_i\subseteq(\RV^\times)^{m_i}$, and a nonempty definable set $I_i\subseteq\Gamma^{n-m_i}$ with
\[
 \vrv(V_i)=\{\beta_i\},\qquad
 h_{M_i}(U_i)=V_i\times I_i^\sharp .
\]
All sets and maps are definable over the parameter base $\mathbb S$.
\end{lem}

\setcounter{thm}{13}
\begin{nota}[Equivariant residue realization]\label{bipo:gdv}
In this notation we work in the field $\puC$ of complex Puiseux series and take $\mathbb S = \C\dpar t$; the value group is identified with $\Q$. Write $\ggk^{\widehat\mu,\mathrm{raw}}\var_{\C}$ for the Grothendieck ring of complex varieties with good $\widehat\mu$-actions, where \emph{good} means that the action factors through some $\mu_N$ and every orbit is contained in an affine open subset. Write $\gmv$ for its quotient by the ideal generated by
\[
 [X\times(\A^r,\rho)]-[X\times\A^r],
\]
for every variety $X$ with a good $\widehat\mu$-action and every linear action $\rho$ of some $\mu_N$ on $\A^r$, where the action on the second affine factor on the right is trivial. For $q\in\Q$, let $L_q=q^\sharp\sqcup\{0_q\}$ be the one-dimensional residue vector space whose nonzero part is $q^\sharp$; its class in $\sggk\RES$ is $[\G_m]+1=[\A]$. By \cite[Notation~7.3]{FY:Fubini}, there is a canonical isomorphism
\[
 \Theta:\sggk\RES\xrightarrow{\ \sim\ }\gmv,
\]
constructed with the finite Kummer actions of $\widehat\mu$ on the points of $\RES$ objects that are rational over the fields $\C\dpar{t^{1/N}}$. If $h_{M_i}(U_i)=V_i\times I_i^\sharp$ is a monomial decomposition of an object $\bm U$ of $\RV[*]$ as in Lemma~\ref{coh:decom}, with $\ell_i$ free $\RV$ coordinates, then \cite[(7.1)]{FY:Fubini}
\begin{equation}\label{twist:C}
 (\Theta\circ\bb E_b)([\bm U])
   =\sum_i\chi_b(I_i)\,\Theta([V_i])[\G_m]^{\ell_i}.
\end{equation}
This is an evaluation of the retraction $\bb E_b$ of Section~\ref{sec:retract}, so it does not depend on the decomposition.
\end{nota}

\begin{nota}\label{mov:vol}
The motivic volume operator is
\[
 \Vol=\Theta\circ\bb E_b\circ\int:
 \ggk\VF_*\longrightarrow\gmv .
\]
Here $\bb E_b$ is applied after the quotient by $(\bm P-1)$, on which it is defined by Section~\ref{sec:retract}.
\end{nota}
'''

EDITS = [
    (r'Invariance and covariance are defined and investigated  in \S~\ref{sec-pscb}, where the surjectivity of the lifting homomorphism (\ref{lifting:hom}) is also established.',
     r'is also established.',
     r'''In \S~\ref{csndag} we recall from \cite{FY:Fubini} the monomial decomposition of definable sets in $\RV$ and the isomorphism $\Theta$, which are used in \S~\ref{sec:spec:pui}. Invariance and covariance are defined and investigated  in \S~\ref{sec-pscb}, where the surjectivity of the lifting homomorphism from $\ggk \mgRV^{\db}[*]$ to $\ggk \mgVF^\diamond[*]$ is also established (Corollary~\ref{L:sur:c}).'''),
    (_start, _end_anchor, NEW_SECTION),
    (r'As in \S~\ref{jp:fubini}, from here on, we work in the field $\puC$',
     r'As in \S~\ref{jp:fubini}, from here on, we work in the field $\puC$',
     r'''From here on, we work in the field $\puC$'''),
    (r'be the one-dimensional residue vector space introduced in the proof of Notation~\ref{bipo:gdv}.',
     r'be the one-dimensional residue vector space introduced in the proof of Notation~\ref{bipo:gdv}.',
     r'''be the one-dimensional residue vector space of Notation~\ref{bipo:gdv}.'''),
    (r'the promised construction of $\Vol_b$ in Remark~\ref{rem:volb} needs correction',
     r'the promised construction of $\Vol_b$ in Remark~\ref{rem:volb} needs correction',
     r'''the promised construction of $\Vol_b$ in Remark~5.18 needs correction''', False),
    (r'parameter-relative $\sggk\RES$ ring appearing in Theorem~\ref{fubini}, rather',
     r'parameter-relative $\sggk\RES$ ring appearing in Theorem~\ref{fubini}, rather',
     r'''parameter-relative $\sggk\RES$ ring appearing in Theorem~5.17, rather''', False),
    (r'\bibitem{hrushovski:kazhdan:integration:vf}',
     r'\bibitem{hrushovski:kazhdan:integration:vf}',
     r'''\bibitem{FY:Fubini}
Arthur Forey and Yimu Yin, {Fubini theorems for motivic volume}, manuscript in the repository \url{https://github.com/daviddhilbert/Fubini-theorems}, file \texttt{paper/fubini-theorems.tex}.

\bibitem{hrushovski:kazhdan:integration:vf}''', 'switch'),
    (r'\bibitem{loeser2019motivic}', None, None),  # filled below
]

# Delete the uncited bibliography item [loeser2019motivic] (its only citation was removed in B08);
# its resolved referee note R160 stays and records the deletion.
_a = _src.index(r'\bibitem{loeser2019motivic}')
_b = _src.index('% BEGIN REFEREE INSERTION R160', _a)
_item = _src[_a:_b]
EDITS[-1] = (_item, _item, r"""\ReviewOnly{The bibliography item loeser2019motivic, no longer cited, is deleted here.}
""")
_r160 = r'}{The entry now gives the published version, Algebraic Geometry \textbf{8} (2021), no.~2, 196--230, with its final full stop.'
EDITS.append((_r160, _r160, _r160 + r' The entry was later deleted: after the removal of the Fubini theorems it is no longer cited.', True, _r160))

RESOLUTIONS = {}
