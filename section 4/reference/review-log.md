# Manuscript review log

The author authorizes direct application of typos and other independently
established clear corrections. Reserve questions for genuine mathematical
decisions or uncertainty. Show at most two items at a time in the main text;
the referee inventory does not limit the independent rereading.

## Historical first display: the two opening corrections

1. **Remark 4.2 / R056 — applied directly.** The exponent in geometric
   Euler characteristic is each cell's dimension. Ambient k cannot serve
   as that exponent for a singleton in Γᵏ. The new cell-decomposition
   description retains the intended invariant and includes dimension zero.
2. **Notation 4.3 / R057 — applied directly.** The graded affine-line
   class and the point class have degree one; the ring unit has degree zero.
   The graded ideal uses the homogeneous degree-one fibre differences.
   This is a clarification of the existing convention, not a new quotient.

These two passages were shown in dark orange for the first display; neither is an
approval request. Their referee notes record that the corrections were
applied under the author's standing authorization.

## Direct editorial corrections

| Location | Finding | Action |
| --- | --- | --- |
| Definition 4.1 / R055 | Plural “objects” with “is” | Changed to “are”. |
| §4.1 component-map paragraph / no referee ID | ε_g^{k,l} uses k where the paragraph fixes n,l | Changed to ε_g^{n,l}; checked against the displayed map. |
| Proposition 4.7 proof / R065 | Singular “existence” with “follow” | Changed to “follows”. |
| Notation 4.13 / R070 | Sentence ends with a comma | Changed to a full stop. |
| Paragraph after Remark 4.4 / R168 | Missing article | Inserted “the”. |

## Deferred

The later mathematical drafts are preserved in `deferred-proposals/`.
They are not pending questions to the author now. Continue checking their
statements and proofs independently, including matters absent from the
referee notes, before choosing the next small batch.

## Subsequent independent pass

R058/R059 were applied after checking integer-bilinear components, full
graded balancing and the degree-zero cancellation. R060's comparison is
now called natural, without an unsupported injection claim. R061's unit
and associativity check, R062's actual degree-zero coefficient group and
R063's degree restrictions are explicit. The sign calculation R064 is
spelled out from the paper's own definitions. The alternative quotient
is named in R066. The sign and endpoint formulas of R067/R068 and the
separate zero-radius proof R071 are applied. R072's diagram composite is
explicit. These are direct corrections under the author's standing
authorization, not pending approval requests.

The author accepted R069: index Pγ by nonnegative radii admitting an
original-base definable RV lift. The reviewed orange proposal is now applied
as ordinary main text, including the same indexing restriction on the
ideal's generating set. The review prompt is removed and the referee item
is marked resolved. There are no pending author questions. Independent
proof work continues.

## Proof-driven independent pass

The actual unary convolution proves all sign and endpoint cases displayed
in Notation 4.11. The bounded generator ideal is exactly the kernel of the
Euler functional, yielding its ℤ quotient. The unary stabilization assertion
is also proved without an Archimedean or HK theorem input. These checks
produced no additional pending mathematical proposal.

The explanatory paragraph inserted after diagram (4.8) left the old trailing
“which may serve” as a sentence fragment. It now begins “This provides”.
This is an editorial repair to our clarification, applied directly.

The later first-order pass proves the unary representation over the original
base in both directions, the corresponding actual convolution ring, bounded
generation and its Euler-kernel quotient. The full graded maps and their
higher-dimensional fibre integrals remain separate obligations.

## Independent correction S4-U003: positive homogeneous degree

The comparison after Remark 4.4 claimed vanishing whenever y is outside
degree zero. That includes mixed-degree elements such as the sum of the
degree-zero unit and a degree-one point. After [A]=1, the positive-degree
contribution vanishes through [G_m]=0, but the degree-zero contribution
survives. The main text now states the intended condition: y is homogeneous
of degree l>0. This is a clear correction applied under the author's
standing authorization, not a pending proposal. The full PDF and a focused
main-text extract are rebuilt. The accepted R069 radius passage is retained
in section4-radius-accepted.pdf.

Formalization update for S4-U003: `RVOrdinaryDimensionFreeEvaluation.geometric_positive_gamma` now proves the corrected vanishing for every homogeneous positive-degree Gamma element on the actual balanced tensor; no global RV descent is inferred.


## Approved T001 follow-through: two colored groups

The author confirmed T001 approval. Read-only review of `section 3`
confirmed the positive quotient presentation, both completed kernel proofs
and the retained Gamma-ground formal scope. Section 4 now uses the
surjections and their coefficient relations rather than tensor inverses.

- **S4-T001-1:** the ordinary tensor assignment identifies translation
  pairs by either numerical Euler characteristic. In Proposition 4.7 the
  target weight sigma_delta(eta)=sigma(eta-delta e_i)-delta preserves the
  corrected weight, so the whole lambda polynomial is unchanged. The
  balanced map therefore identifies every generating kernel pair; P and h
  are computed with explicit tensor preimages. No extra RES quotient is
  added for this descent.
- **S4-T001-2:** replace the bounded tensor-isomorphism assertion by its
  product homomorphism, and define the bounded measured retraction as the
  full graded ordinary bounded-Euler map after forgetting volume. The RES
  restriction and the accepted P_gamma cancellation follow directly. The
  positive-radius tensor calculation is an image formula; the separate
  zero-radius proof is retained.

These are applied consequences of the approved correction and independently
checked invariance; no additional approval question is pending. They remain
orange in the main text for the author's reading. The focused extract has
only the five pages containing that review color, with exact page-text
matching against the rebuilt full manuscript. The approved Section 3 statement and both proofs were subsequently synchronized
verbatim from the upstream adoption record (6924 characters), retaining its
green author resolution. The review-only notes were excluded. Section 3's
Lean code remains on the other executor.
