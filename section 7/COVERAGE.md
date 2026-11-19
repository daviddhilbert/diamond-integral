# Section 7 coverage

Manuscript: `section 2/reference/diamond_integral_revision_annotated.tex`, §7
(`section:int`). Plan and author decisions: [PLAN.md](PLAN.md).

Status key: **done** = complete numbered result in the stated scope, no input
beyond the ACVF model; **partial** = some clauses done; **pending** = not yet
formalized.

| Number | Label | Status | Lean |
|---|---|---|---|
| Notation 7.1 | `punc:RVd` | done (as data) | Section 4 `AnnularBlowup.shellPoints`, `endpointPoints` |
| Definition 7.2 | `defn:blowup:coa` | done on classes | Section 4 `RelativeAnnularGenerators.AnnularDatum` (data, `annularObject` = U^{τ,j}); `ElementaryBlowups.datumRes`/`datumCres`, `cls_annular_split` (restriction); `ElementaryBlowups.ElementaryStep`, `Step` (length one); `BlowupCongruence.BlowupSteps` (length n) |
| Remark 7.3 | — | pending | approved scope: dimension claim only |
| Remark 7.4 | `db:blowup:bound` | partial | first claim: Section 4 `shell_domain_bounded`, `endpoint_domain_bounded`; named-bound converse pending |
| Lemma 7.5 | `elementary:blowups:preserves:iso:vol` | done | `BlowupResults.lemma_7_5`; construction in `ElementaryComparison` (`ratioAperture`, `secondDatum`, `shallowIso`, `deepIso`, `endpointIso`, `step_of_le`, `elementaryDiamond`) |
| Corollary 7.6 | `eblowup:same:loci:iso` | done | `BlowupResults.corollary_7_6` (`ElementaryBlowups.step_diamond`, via matrix refinement `Refinement.refine_matrix`) |
| Lemma 7.7 | `blowup:equi:class:coa` | done | `BlowupResults.lemma_7_7` |
| Corollary 7.8 | `blowup:equi:class` | done | `BlowupResults.corollary_7_8` |
| Definition 7.9 | μIsp^db | done | `BlowupCongruence.MuIsp` |
| Lemma 7.10 | `isp:congruence:vol` | partial | additive congruence `BlowupResults.lemma_7_10_addCon`; product compatibility pending |
| Lemma 7.11 | `special:to:blowup:coa` | pending | approved: partial-lift form |
| Lemma 7.12 | `blowup:same:RV:coa` | pending | morphism part: `ChartLifting.chart_iso_lift` |
| Lemma 7.13 | `kernel:dim:1:coa` | pending | approved: head-start form |
| Lemma 7.14 | `isp:VF:fiberwise:contract` | pending | |
| Corollary 7.15 | `contraction:same:perm:isp` | pending | |
| Definitions 7.16, 7.17, 7.19 | `rvaffine`, `defn:balance`, `def:units` | pending | |
| Remark 7.18 | `2cell:linear` | pending | approved scope: ∞-symmetry and slope |
| Lemmas 7.20–7.23 | `decom:into:2:units` … `contraction:perm:pair:isp` | pending | |
| Proposition 7.24 | `kernel:L` | pending | |
| Remark 7.25 | `thekernel` | pending | |
| Theorem 7.26 | `main:prop` | pending | |
| Corollary 7.27 | `db:to:novol` | pending | |
| Remark 7.28 | `eg:eb:factor` | pending | author: crucial; report if blocked |

Supporting modules: `BoundedClasses` (isomorphism classes of μRV^db[k] as a
commutative monoid, restriction and gluing of isomorphisms, refinement),
`RVMaps` (definability of RV maps and valuation comparisons), and the
Definition 6.34–6.37 chart lifts `MeasuredRVBridge`, `MeasuredRVBounds`,
`ChartLifting`, `ChartDiamondLift`.
