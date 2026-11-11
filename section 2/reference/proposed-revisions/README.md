# Review record: approved section 2 revisions

Author clarification, November 9, 2026: the intended exchange assertion is
scalar. In 2.15, the literal wording “A, B are subsets of VF” (likewise RV)
already specifies one coordinate. The general tuple convention does not
turn those literal subsets into multivariate subsets.

## R025: accepted clarification

The introductory sentence of 2.14 now says that exchange concerns single
elements over the same fixed parameter base. The two existing bullets are
unchanged. R025 is resolved with the original referee text gray and a brief
author resolution green. R025-exchange.patch records the approved change.

## R026: resolved by author interpretation; proposed rewrite withdrawn

The statement and proof of 2.15 are unchanged. Its author resolution records
that both source and target are literal unary VF or RV subsets, as the
original wording already intends. All algebraic closures use the fixed base.

R026-unary-source.patch is retained only as the superseded proposal; it was
not applied. In particular, its proposed explicit tuple-target extension
is not the author's adopted statement.

The current resolved passage is in
[the PDF extract](../section2-exchange-resolved-review.pdf), printed page 14.

## R029: two approved proof corrections

The author approved replacing the individually definable point claim in
2.24's proof with the algebraic-point/finite-ground-definable-set contradiction,
and adding “proper” to its final sentence. Both edits are applied; the
statement is unchanged. `R029-proof-corrections.patch` records only these two
proof edits for review; the working source already contains them.

The referee annotation is marked partly resolved: its separate question
about additional DC ground parameters has not been settled. The original
referee text remains gray and the brief author explanation is green.
[The focused PDF](../lemma-2-24-resolved-review.pdf) shows printed page 16.
`AtomicDiscs.lean` proves the unary real/Gamma-base case without a
nontrivial-ground-value-group premise or an atomic-base-change input.

## R028: paper-wide standing-base revision approved and applied

The author approved nontrivial Γ(S) throughout the paper. The three main
changes are applied: §2's standing paragraph, its VF-generation discussion,
and the removal of the trivial-ground parenthetical in **§6**, “Special
covariant bijections.” The R028 note records the adopted resolution.
Earlier review messages misnumbered that §6 passage as §5.

The focused [approved PDF](standing-ground-assumption-review.pdf) contains
printed pages 11, 13, 15 and 48. The exact applied patch is
`R028-standing-ground-assumption-applied.patch`; it was checked against the
previous audited manuscript hash. `R028-standing-ground-assumption.patch`
and `ground-base-assumption-review.tex` retain the historical proposal, and
`standing-ground-assumption-proposal.pdf` retains its original PDF. They
are superseded by the applied revision.

The author asks us to track any later genuine need for triviality, rather
than drop the standing assumption silently.

## R163: thin-annulus definition approved and applied

The approved paragraph before 2.27 defines a thin annulus as the finite-radius
shell `C(a,γ) \ O(a,γ) = {x : val(x−a)=γ}`. R163 is marked resolved, with
the original text gray and a brief author explanation green. The focused
[approved PDF](thin-annulus-review.pdf) shows printed page 16.
`thin-annulus-proposal.pdf` preserves the historical proposal;
`R163-thin-annulus.patch` records its definition insertion, now applied.

## R030 and zero branch tags: approved and applied

The author approved both changes: 2.29 now uses the coordinate-chain proof,
and the tag ranges in 2.29 and 2.30 include RV∞. The constant zero branch is
retained. R030 is marked resolved with its original text gray and a brief
author explanation green. `R030-coordinate-chain-applied.patch` records the
exact applied change, including the resolution note.

The [approved extract](coordinate-chain-review.pdf), printed pages 16–19,
shows the current manuscript. `coordinate-chain-proposal.pdf`,
`coordinate-chain-review.tex` and `R030-coordinate-chain.patch` preserve the
historical proposal. R031's separate disc-parameter and compactness issues
are not covered by this approval and remain open.

The author notes a similar proof pattern in *Generalized Euler characteristic
in power-bounded T-convex valued fields*. Its different setting does not
supply an ACVF theorem; no cross-context result is imported. A general
coordinate-chain lemma is being proved separately in Lean. No additional
numbered main-text lemma has been inserted without review. The general ACVF
image lemma and 2.29 are now compiled and audited in their recorded scope.

## R031: disc parameters and compactness approved and applied

The author approved all three corrections in Corollary 2.30: full branch
graphs may name the disc together with the RV tag; the proof cites corrected
2.29; and its uniformly coded compactness property is explicit. The proof
includes empty fibers through the finite disjunction over 0≤k≤N tags.
R031 is marked resolved, with the original referee text gray and a brief
author explanation green.

The [approved extract](disc-parameters-review.pdf) shows printed pages
16–19. `R031-disc-parameters-applied.patch` records the exact applied edits
and resolution note. The historical proposal is retained in
`disc-parameters-proposal.pdf`, `disc-parameters-review.tex` and
`R031-disc-parameters.patch`. Its PDF open request returned queued, not a
display confirmation. This textual resolution does not claim the general
DC-base Lean formalization of 2.25 or 2.30 has been completed.

## R032–R033: boundary definition and proof approved and applied

The author approved both revisions. R032 explicitly calls the original set
definable. R033 gives one VF representative per boundary RV tag, states
constancy of the finite RV-image set along each source RV fibre, and applies
2.30 separately on zero-coordinate faces. The proof retains input tags in
each graph, includes the zero-arity case using the approved −∞ convention,
and spells out the coordinate-chain coverage.

Both annotations are marked resolved, with the original referee text gray
and brief author explanations green. The [approved PDF](rv-boundary-review.pdf),
printed pages 19–20, includes the continuation of the original annotation.
`R032-R033-boundary-applied.patch` records the exact applied change.
`rv-boundary-proposal.pdf`, `rv-boundary-review.tex`, and the original
`R032-R033-boundary.patch` preserve the historical proposal. Its panel-open
request returned queued. This does not claim a complete Lean proof of the
higher-dimensional boundary dimension lemma.

## R034: approved tuple valuation and zero increment

The author approved and the working manuscript applies the minimum coordinate
valuation in differentiability, the zero-tuple value ∞, and exclusion of b=0.
The input-first ijth partial derivative has derivative-matrix position (j,i).
The coordinatewise valuation image in boundedness remains distinct.
The original referee text is gray and the brief author explanation green.

[Approved PDF](tuple-valuation-review.pdf) and
`tuple-valuation-resolved-review.pdf`, printed pages 20–21, were rebuilt from
the applied manuscript. `R034-tuple-valuation-applied.patch` records the exact
change. `tuple-valuation-proposal.pdf`, `tuple-valuation-review.tex` and
`R034-tuple-valuation.patch` preserve the historical proposal. The right-panel
open request returned queued. R035–R036 are also approved and applied.


## R035: approved square dimensions and generic RV constancy

The author approved the equal-VF-arity hypothesis in Lemma 2.38 and the proof
using generic local constancy of output RV labels before differentiating on
open fixed-label charts. The proof records definability and dimension control
of the exceptional locus and the zero-arity determinant. The original referee
text is gray with a brief green author explanation.

[Approved PDF](jacobian-local-constancy-review.pdf) and
`jacobian-local-constancy-resolved-review.pdf`, printed pages 20–21, are rebuilt
from the applied manuscript. `R035-jacobian-local-constancy-applied.patch`
records the exact change. The historical proposal remains in
`jacobian-local-constancy-proposal.pdf`, `jacobian-local-constancy-review.tex`
and `R035-jacobian-local-constancy.patch`. The panel request returned queued.
This is manuscript approval, not a claim of a complete mixed-map Lean 2.38.

## R036: approved coordinatewise valuation image

The author approved and the manuscript applies `valim(A)` for the coordinatewise
valuation image, reserving `A_Γ` for projection to existing Γ coordinates.
Bounded and doubly bounded now explicitly mean the corresponding property for
some finite Γ bound. This remains distinct from the analytic minimum tuple
value. No later main-text occurrence of the valuation-image notation needed
replacement. The original referee text is gray with a brief green explanation.

[Approved PDF](coordinatewise-valuation-image-review.pdf) and
`coordinatewise-valuation-image-resolved-review.pdf`, printed page 21, were
rebuilt from the applied manuscript. The exact change is in
`R036-coordinatewise-valuation-image-applied.patch`. The historical proposal
remains in `coordinatewise-valuation-image-proposal.pdf`,
`coordinatewise-valuation-image-review.tex` and
`R036-coordinatewise-valuation-image.patch`. The panel request returned queued.

## R037: resolved using the author's induction

After explaining the original induction, the author instructed continuation.
The manuscript now spells out γ_t as the finite supremum of the absolute
output values on each nonempty fibre. The least-upper-bound formula makes the
bound function definable, and the unary Γ-valued case bounds all fibres.
The original unary argument is retained. The referee text is gray and the
brief author explanation green.

[Adopted PDF](inductive-bounded-image-review.pdf) and
`inductive-bounded-image-resolved-review.pdf`, printed pages 21–22, were rebuilt
from the applied manuscript. `R037-definable-fibre-bounds-applied.patch` records
the exact adopted change. The panel-open request returned queued.

The earlier `uniform-bounded-image-review.pdf`, its TeX source, and
`R037-uniform-bounded-image.patch` are historical alternatives. The author
pushed back on replacing the induction, and that replacement was withdrawn
as a required repair. Do not apply it from the old approval question.

## R038: approved affine local limit sets

The author approved using all of L in the punctured-neighborhood formula and
allowing that formula locally without a global range bound. A finite affine
limit set gives boundedness on a punctured neighborhood; separate boundedness
hypotheses still mean the union of all values is bounded. Minimality and the
puncture are unchanged. The original referee text is gray with a brief green
explanation.

[Approved PDF](local-limit-sets-review.pdf) and
`local-limit-sets-resolved-review.pdf`, printed page 22, were rebuilt from the
applied manuscript. `R038-local-limit-sets-applied.patch` records the change;
`local-limit-sets-proposal.pdf`, `local-limit-sets-review.tex` and
`R038-local-limit-sets.patch` preserve the proposal. At the author's request,
a copyable explanation was supplied for the Special transformations session:
its current Lean `Section9/Limits.lean` already uses all of L and has no global
boundedness premise. No edit or push to that manuscript was performed here.

## R039: finite branch continuity and positive arity approved and applied

The author approved the proof expansion and n>0 restriction. The proof keeps
the finite RV coding and treats all labels on a locally constant finite-label
neighborhood; empty labels give the empty continuous correspondence. The
author explains the original proof via the RV-indexed union dimension bound,
which obtains the same coverage. The positive-arity restriction respects the
unchanged puncture and minimality conventions. The original referee text is
gray and the short adopted resolution green.

[Approved PDF](finite-branch-continuity-review.pdf) and
`finite-branch-continuity-resolved-review.pdf`, printed pages 22–23, were rebuilt
from the applied manuscript. `R039-finite-branch-continuity-applied.patch`
records the exact adopted change. The old proposal is retained as
`finite-branch-continuity-proposal.pdf`, its review TeX and the original patch.
The RV-union principle and finite continuous branch minimal-limit step now
compile in Lean in the scopes recorded in STATUS.md; full 2.44 remains.

## R040/R165: local curve-selection hypothesis and proof approved and applied

The author approved local VF-generation and the proof. Lemma 2.46 explicitly
takes definable A⊆VF^n and requires finite nonempty values converging to {b}.
Projective charts handle infinite coordinates, and a constant finite nonempty
correspondence on a clopen complement extends the continuous germ without
assuming a definable scalar realizing every definable radius. Nontriviality
remains standing; VF-generation remains local. The original referee text is
gray and the short adopted explanations green.

[Approved PDF](curve-selection-base-review.pdf) and its resolved copy show
printed page 24. `R040-R165-curve-selection-applied.patch` records the adopted
change; `curve-selection-base-proposal.pdf`, its review TeX and original patch
preserve the historical proposal. The main PDF was rebuilt in three passes.
The display requests returned queued. The full Lean 2.46 choice construction
and projective-chart transport are not yet claimed.

## R041/R042: geometric revisions approved and applied

The author approved both revisions. The closed bounded image proof treats
finite missing affine boundary points and unbounded output separately, with
finite nonempty choices over a temporary VF-generated base. The closed-graph
criterion makes the intended projective ambient space explicit: affine target
B, graph closure in A×B^p. Its proof selects bad inputs first and takes a
finite projective limit of their images. The limit remark uses the projective
line with valuation topology. No global VF-generation hypothesis is added.
Both annotations are resolved gray/green with brief explanations.

`R041-R042-geometric-proofs-applied.patch` records the exact adopted edits;
`geometric-closedness-proposal.pdf`, the review TeX and original patch preserve
the historical proposal. The main PDF was rebuilt in three passes.

## R166: eventual affine wording approved and applied

The author separately approved the piecewise rational-affine formulation.
One affine piece remains near an endpoint, explaining the obstruction to
approaching (∞,0). The example and conclusion are unchanged. The annotation
is resolved gray/green and the exact adopted edit is
`R166-eventually-affine-curves-applied.patch`.

[Approved PDF](geometric-closedness-review.pdf) and its resolved copy show
printed pages 25–27, including R166 and R041/R042. The main PDF was rebuilt
in three passes after R166. The panel request returned queued.

## Independent proof review comes first

The author requires independent checking of the main statement and proof,
with its conventions and cited hypotheses, before assessing referee remarks.
The rule is permanent in root AGENTS.md. Literal subsets of VF or RV are
already unary; no arity amendment is inferred from the tuple convention.

## R043/R044: author-agreed proof details applied

The author confirms that the paper proofs are quick and these comments spell
out details. The expanded proofs retain both statements and proof strategies.
R043's arity objection is withdrawn. The other R043 details explain singleton
limits and the inverse tail-radius laws; R044 spells out the lower bound,
finite nonempty choices, the limit-point contradiction and the uniform
endpoint bound. The original annotations are gray and the author explanations
green; they do not classify the original statements as false.

`R043-arity-objection-withdrawn.patch` records the initial annotation
correction; `R043-R044-proof-details-applied.patch` records the applied proof
expansions and final resolutions. [Approved PDF](annuli-partition-bounds-review.pdf)
and the resolved copy show printed pages 27–29. The main PDF was rebuilt
three passes and queued for the right panel.

`annuli-partition-bounds-proposal.pdf`, the original review TeX and
`R043-R044-annuli-partition-bounds.patch` preserve the earlier proposal.
`annuli-partition-original-proofs-review.tex/.pdf` preserve the independent
comparison, when both main proofs were checked byte-for-byte against the
uploaded manuscript before expansion. These are historical, not active
unapplied edits.

## R045: independent fibrewise-openness proof approved and applied

The author approved the proof. It retains the statement and bad locus,
using valid-radius sets and the RV-indexed union principle to obtain one
radius on a disc of base points. Finite nonempty choices and unary generic
continuity produce an open product inside A meeting S. It avoids a
codimension-one assumption and a minimum-radius choice. The fixed unary base,
with empty fibres allowed, makes the closed case follow by relative complement.
The original annotation is gray with a brief green author explanation.

`R045-fiberwise-openness-applied.patch` records the exact adopted change;
`fiberwise-openness-proposal.pdf`, the review TeX and original patch preserve
the proposal. [Approved PDF](fiberwise-openness-review.pdf) and the resolved
copy show printed pages 29–30. The main PDF was rebuilt in three passes;
the display request returned queued. Full Lean 2.54 remains in progress.

## R046: relative fibre-graph closure details approved and applied

The main proof was checked independently first. Its original implication
works through relative-family closure. The author approved the expansion,
which takes ambient closures of fibre graphs in two affine projective charts
and intersects with the original domain before the closed-graph criterion.
The statement and “as in Lemma 2.54” are retained.

`R046-fiberwise-continuity-applied.patch` is the exact adopted change;
`.scratch/pre-r046-approved.tex` is the backup. The original proposal PDF,
review TeX and proposal patch preserve the history. The
[approved PDF](fiberwise-continuity-details-review.pdf) and resolved copy
show printed pages 30–31. The main PDF was rebuilt in three passes; the
right-panel display request returned queued. Full Lean 2.55 remains open.

R021 was resolved using the existing author-approved scalar-scope reading;
`R021-existing-arity-clarification.patch` changes only its annotation. The
main tuple convention is unchanged. The §2 review pass now reaches its end;
R029's additional DC-base scope is the one partly resolved annotation.


## R029: extra disc parameters via accepted [18, Lemma 3.9]

[Unapplied focused PDF](disc-ground-base-review.pdf), printed pages16–17,
and its TeX source add one green clarification in the proof of2.24.
For previously named disc parameters, set-valued RV constancy in [18 3.9]
gives the unary assertion directly. The existing real/Gamma proof and product
induction remain. This uses the author's accepted prequel results and adds
no hypothesis to2.24. The corresponding finite-disc-ground Lean theorem and
product induction have passed the audit. It avoids asserting that2.21 itself
extends to arbitrary imaginary ground bases. Main-text approval is pending;
the working manuscript and its partly-resolved R029 annotation are unchanged.
The focused PDF is queued right; visibility is unconfirmed.


The author approved the R029 clarification. It is now applied to the working
main text, and R029 is fully resolved with the brief cited-result explanation.
[Approved current extract](../disc-ground-base-resolved-review.pdf), printed
pages 16–17. The draft above is preserved as review history. The 796/373 Lean
audit remains current; no Lean source changed when applying this approval.
