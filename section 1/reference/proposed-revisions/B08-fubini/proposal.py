"""Batch B08: the Fubini theorems leave the paper (R019); front matter and introduction.

Author's decision (November 22): the Fubini theorems have been moved to a separate repository and
are not covered by this paper.

Independent reading. In the front matter and introduction the Fubini theorems appear in
- the acknowledgement to Johannes Nicaise "for suggesting to work on the Fubini theorem";
- the paragraph that announces Section 5 ("original-language monomial decomposition ... two
  Fubini theorems that are not related to the rest of the paper"), the unnumbered theorem, the
  paragraph on Vol_b and Theorem fubini, and the paragraph on applications ([loeser2019motivic],
  motivic Donaldson-Thomas theory).
All of these are removed. The monomial decomposition (Lemma coh:decom), which is used in Section 8,
is announced in the outline of the paper (batch B09). R019 (the meaning of Vol_b) is resolved by
the removal. R018 stays resolved; its note records the later removal.

The Fubini material of Section 5 itself, and the references to Theorem fubini and Remark rem:volb
in the referee text of R019, are handled in a later batch (B10), which restructures Section 5.

A deletion leaves nothing to colour, so the review copy carries short bracketed notes at the
places of the deleted text (\\ReviewOnly, dropped when the batch is applied).
"""

TITLE = 'Section 1 review B08: the Fubini theorems are removed'
ANCHORS = ['Many thanks to', 'also used in', 'Meaning of the relative volume']
SELECT = True

EDITS = [
    (r' We also thank Johannes Nicaise for suggesting to work on the Fubini theorem.',
     r' We also thank Johannes Nicaise for suggesting to work on the Fubini theorem.',
     r'''\ReviewOnly{The sentence thanking Johannes Nicaise for suggesting the Fubini theorem is deleted here.}'''),
    (r'In \S~\ref{csndag}, we prove an original-language monomial decomposition',
     r'\end{thm*}',
     r'''\ReviewOnly{The paragraph announcing the two Fubini theorems of Section 5 and the unnumbered Fubini theorem are deleted here.}'''),
    (r"}{The second morphism is now $f' : A' \fun B$.",
     r"}{The second morphism is now $f' : A' \fun B$.",
     r"}{The second morphism is now $f' : A' \fun B$. The theorem was later removed together with the Fubini theorems; see R019.",
     True, r"}{The second morphism is now $f' : A' \fun B$."),
    (r'Here the operator $\Vol_b$ is similar to $\Vol$',
     r'definition of $\Vol_b$.',
     r'''\ReviewOnly{The paragraph on the operator Vol-b and on the general version of the Fubini theorem is deleted here.}'''),
    (r'Some property of this form is needed in \cite{loeser2019motivic}.',
     r'along the line of \cite{Nic:Pay:trop:fub}.',
     r'''\ReviewOnly{The paragraph on applications of the Fubini theorems is deleted here.}'''),
]

RESOLUTIONS = {
    '019': r'By the authors\' decision, the Fubini theorems are not part of this paper. The introductory Fubini theorem, the paragraph on $\Vol_b$ and the paragraph on applications of these theorems are removed, so no relative volume is needed.'.replace("\\'", "'"),
}
