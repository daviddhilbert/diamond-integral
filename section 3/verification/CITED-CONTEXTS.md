# Cited source contexts checked during formalization

The author-accepted sources are those in ../../ACCEPTED-CITED-RESULTS.md.
No new global logical premise or blanket acceptance of HK has been added.

## [18]: Integration in algebraically closed valued fields

Source: [arXiv:0809.0473v2](https://arxiv.org/pdf/0809.0473),
29 December 2010, printed pp. 3, 21–27.

The author reports sections 1–3 complete in
[daviddhilbert/integration-in-ACVF](https://github.com/daviddhilbert/integration-in-ACVF).
This consumer pins `3c3e478cf1f298061c4489cc03f95669d551ce5e`.
`IntegrationInACVFExports` connects the original checked theorem types;
local presentation adapters are checked separately before an old input is
reported discharged. Section 1 is introductory. This checkpoint does not
supply the section 6–7 integral/kernel results below. The exact upstream
scope, including the ordinary-source boundary in 3.17 and the approved
ordinary closed-parent statement in 3.24, is retained.

The ambient context is pure characteristic zero, sufficient saturation, a
small base with nontrivial value group, and (outside its §3) the stipulated
(VF,Gamma)-generation. Proposition 6.18 and Theorem 6.19 concern the
unmeasured positive lift/kernel comparison. The following discussion
identifies the single generating pair. Theorems 2.35–2.36 explicitly include
the Gamma-volume categories for object/class lifting. The opening of §7
states the extension of its final results to the other relevant volume
categories; Propositions 7.8–7.10 and Theorem 7.13 give the measured
comparison and principal relation. Reuse must identify the actual
categories, degree conventions and Gamma variant, with the generation
hypothesis retained. The explicit interfaces in `CitedUnmeasuredIntegral`, `CitedBoundedIntegral`
and `CitedMeasuredIntegral` now specialize these comparisons to a small
VF-generated real substructure. Their real-base consequences retain these
replaceable inputs. The corresponding full VF/Gamma-generated context
records, actual graded/filtered comparisons and colimit identifications
are now implemented in the GammaGround variants described below.
Independent disc-name extensions are outside the default §3 context.

`GammaGroundCitedUnmeasuredIntegral` additionally formulates the accepted
unmeasured comparison over the complete Gamma ground. Its explicit context
retains a genuinely VF-generated real substructure, a small Gamma subgroup
containing the values of named RV points, saturation, characteristic zero
and nontriviality of the full Gamma ground. Nontriviality of the real
VF-generated part is not substituted for the last condition. The object
formula uses the actual inverse-image lift over all these parameters.
The positive and group-completed integral consequences, their object
characterization and uniqueness are proved relative to this replaceable
input. The universal presentation is also compared to the actual VF filtration
and its additive/group colimits in GammaGroundVFSemiringColimit and
GammaGroundGradedIntegral.
`GammaGroundSyntaxBridge` identifies RV-tuple definability with the
existing complete Gamma-parameter syntax. The mixed VF/RV syntax, finite-name diagrams and already-definable
interpreted-name transport are now also implemented. Independent disc
names are not silently identified with real or Gamma names.

`GammaGroundCitedMeasuredIntegral` now states both global and fixed-degree
measured inputs in the complete Gamma-ground context. The measured VF
groupoids use actual pointwise preserving cofull partial bijections, with
the exact manuscript-dimension agreement quotient. Their comparison with
the generic presentation is proved locally. Degree zero retains every
Gamma form and uses genuine bijections. Positive and ring integrals,
object characterizations and uniqueness are derived relative to the global
input; the degreewise input gives additive integrals and their analogous
characterization and uniqueness.
`GammaGroundCitedBoundedIntegral` uses the bounded discussion preceding
Theorem 6.19, actual finite direct sums of RV scissors and dimension-bounded
VF scissors. It proves transition compatibility using generator
extensionality. The valuation topology remains explicitly compatible with
the model predicate. The actual Gamma-ground graded/direct-sum and filtered-colimit
identifications are proved in GammaGroundGradedIntegral, retaining every
accepted global, degreewise and bounded lift record explicitly.

## [19]: Integration in algebraically closed valued fields with sections

Source: [arXiv:1204.5979v2](https://arxiv.org/pdf/1204.5979),
20 May 2012, printed pp. 4, 7–8, 11–12.

Convention 2.9 and Remark 2.28 use a VF-generated underlying base. The
piecewise integral-affine discussion distinguishes contraction maps from
arbitrary Gamma-definable functions. Lemma 2.29 is an abstract
integral-domain/torsion-free-module result with explicit closure assumptions
on a class of functions. Its use at the present paper's broader base scope
requires an argument; that scope is not silently imported.
`GammaAffineClassification` keeps the VF-generated real-base restriction
and records both the unary contraction formulas and the unimodular-matrix
classification with values of named RV points as translation constants.

Definition 3.20 and Proposition 3.21 concern categories in an expansion
with a cross-section, with different Gamma objects, arrows and tensor
factors. They therefore cannot simply replace the present paper's
Proposition 3.18. The latter still needs its actual balanced maps,
comparisons and mathematical isomorphism proof.

## HK: Integration in valued fields

Source: [arXiv:math/0510133v3](https://arxiv.org/pdf/math/0510133),
28 April 2006, printed pp. 90–95. This source has been consulted; it has
not been added to the author-accepted input list. The author explicitly
requires local proofs of all needed HK results; no acceptance question is
pending. HK and arXiv:1509.07695 Section 4.2 supply proof ideas only.

Lemma 10.1 discusses the Gamma-to-RV embedding. Corollary 10.3 is the
unmeasured graded tensor comparison. Proposition 10.10(1) is its
Gamma-measured counterpart. The surrounding context is the induced RV
structure with its explicit base restrictions and the hypotheses of
Lemma 3.26. Part 10.10(2) is explicitly rejected by the present manuscript
and must not enter the dependencies. The elementary tagging, scissor
descent and RES inclusion proved locally do not supply the remaining
Gamma embedding or tensor isomorphism.

## [20]: Fourier transform of the additive group

The accepted source [arXiv:0903.1097v3](https://arxiv.org/pdf/0903.1097v3),
23 March 2014, printed pp. 8–10, was also checked for a possible direct
source of the outstanding tensor comparison. Its Definition 2.10 restricts
RES coordinates to the residue field and fixes the Gamma volume component
to zero. The tensor discussion preceding Theorem 2.13 refers to the
cross-section work [19]. These are different categories from the full
Gamma-volume and finite-value-support categories in the current manuscript.
No tensor input has been transferred from this source.


## [23]: Reichstein–Youssin, birational diagonal actions

The author explicitly approved adding the proof and this dependency on
November 12. Published source: Z. Reichstein and B. Youssin, *A birational
invariant for algebraic group actions*, Pacific J. Math. **204** (2002),
no. 1, 223–246, DOI [10.2140/pjm.2002.204.223](https://doi.org/10.2140/pjm.2002.204.223).
The [publisher PDF](https://msp.org/pjm/2002/204-1/pjm-v204-n1-p12-p.pdf)
and [arXiv version](https://arxiv.org/pdf/math/0007181) were checked directly.
Corollary 2.5 is on journal p. 229; Theorem 7.1 is on pp. 238–239.
The bibliography entry is appended as [23], preserving accepted [18]–[22].

`ReichsteinYoussinInput.classification` states precisely the consequence
for faithful diagonalizable representations in characteristic zero:
equivariantly birational rational function fields imply weight tuples
related by an integer matrix of determinant ±1. The joint finite weights
generate the character group, and faithfulness of both actual character
actions is explicit. `DiagonalBirationalKernels` proves that faithfulness
from joint generation and the rational intertwiner; it is not an ACVF
premise. The classified monomial isomorphism can differ from the given
birational map.

No HK result is assumed. The ACVF normalization, generic-fibre matching,
character-twist invariance and return to the original ground must be
proved locally; none is included in the cited structure.


The complete local ACVF bridge is now proved, including finite tagged
generic-family bijections and inverse compatibility, actual old-ground
coefficients, compactness, and full bijective RV lifts.
`GammaGroundCoefficientClassification` merely specializes the approved
R--Y field/group input to the manuscript's actual ground context; residue
characteristic zero follows from ACVF00. Both ordinary horizontal
positive coefficient monomorphisms are proved. Their updated 977-module integrated
audit passes. Neither [19] nor R--Y is needed for well-definedness
of the lower map itself.


## Completion review

Both full-ground statements of Remark 3.15 now have local proofs using
the already approved R--Y input; see GammaGroundGammaAffineClassification
and GammaGroundIntegralAffineCodeContractions. The latter covers arbitrary
source and target tuple arities, including nonbijective contractions and
rectangular integer matrices. The old [19] interface keeps
its original real VF-generated scope. Neither classification input is
used for well-definedness of the lower coefficient map. The reviewed
§3 coverage is recorded in paper-targets.json, independently of numerical
export counts. Later [18] geometric kernels and [23] classification remain
accepted cited inputs, and no independent proof of them is claimed.


## [18] refresh and push authorization — 2026-11-12

The author explicitly skips the supplementary unary-ray refinement and
requests an upstream check, complete audit and push. The dependency is now
pinned at 7d4acc730496b3bd05a22c268ffd89540ca694f9. The previously reused
section 2–3 files are unchanged. Section 4 is checked and section 6 now
supplies finite RV integration, kernel and principal-ideal proofs relative
to its explicit unfinished section 5.8 input. Section 7 measured integration
is not available.

IntegrationLaterExports links ten exact section 6 declarations; their full
types retain Section5TwoOrderInputAll, native finite RV/VF categories and
VFGammaGeneratedBase. The last condition explicitly requires definable
closure of the generating base. GammaGroundContext records a generated
real substructure and a Gamma subgroup, without that closure equation.
The existing lift-input records therefore remain explicit until both the
closure transport and native/consumer category comparisons are compiled.
No legacy input is silently claimed discharged by an export alias.

The already approved proper-open-radius compatibility patch covers nine
dependency files. Numbered statements are unchanged; two auxiliary obstacle
premises now use proper OpenRadius, matching their corrected predecessor
producers. Other edits are confined to proof bodies. The patch, auxiliary
API changes, file hashes and base revision are recorded explicitly. CI now
prepares both dependency patches and runs both section audits.

The main branch's independent section 2 citation update was fast-forwarded
and reconciled with this work. The approved manuscript remains unchanged.
Both combined section audits passed before the authorized push to origin/main.


## Verified upstream refresh prepared for publication — 2026-11-12

Both section audits pass at the pinned Lean 4.35.0 toolchain. Section 2
retains 850 theorem exports and 378 selected reuse declarations. Section 3
checks 2,866 theorem types, 2,280 definitions, 170 named instances and eight
reused declarations: 5,324 heads across 1,003 supporting modules plus Section.
The receipt validates 36 native [18] export links and the 21 manuscript
targets with 119 declaration links. Only the permitted standard logical
principles occur. Both compatibility patches also apply to their clean
dependency indexes.

The native section 6 theorem types retain the unfinished Section5TwoOrderInputAll
and exact generated-closure/category conditions. Legacy lift/kernel records
remain explicit pending the checked comparisons; section 7 measured inputs
are not claimed discharged. No HK input or manuscript change is introduced.
The author explicitly skips the unary-ray refinement. CI now prepares both
patches and audits both sections, with the same 180-minute build allowance
as the upstream project. This record reports local verification; CI is
reported separately after publication.
