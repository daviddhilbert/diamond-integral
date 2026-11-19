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
| Remark 7.3 | — | done (approved scope: dimension claim) | `Remark73.remark_7_3`, `remark_7_3_lt`: with Section 2's RV dimension, `dim_RV U ≤ k < 1 + k` when U has an elementary annular blowup |
| Remark 7.4 | `db:blowup:bound` | done | `Remark74.remark_7_4_bounded`; `Remark74.remark_7_4_named` (a bound named over the base, via Section 6 `bounded_gamma_rows_named_bound`) |
| Lemma 7.5 | `elementary:blowups:preserves:iso:vol` | done | `BlowupResults.lemma_7_5`; construction in `ElementaryComparison` (`ratioAperture`, `secondDatum`, `shallowIso`, `deepIso`, `endpointIso`, `step_of_le`, `elementaryDiamond`) |
| Corollary 7.6 | `eblowup:same:loci:iso` | done | `BlowupResults.corollary_7_6` (`ElementaryBlowups.step_diamond`, via matrix refinement `Refinement.refine_matrix`) |
| Lemma 7.7 | `blowup:equi:class:coa` | done | `BlowupResults.lemma_7_7` |
| Corollary 7.8 | `blowup:equi:class` | done | `BlowupResults.corollary_7_8` |
| Definition 7.9 | μIsp^db | done | `BlowupCongruence.MuIsp` |
| Lemma 7.10 | `isp:congruence:vol` | partial | additive congruence `BlowupResults.lemma_7_10_addCon`; product compatibility pending |
| Lemma 7.11 | `special:to:blowup:coa` | done (full lift, on classes) | `SpecialChainInduction.lemma_7_11`: for a relative aperture chain on the lift of a doubly bounded U ∈ μRV^db[1+k], the contraction U_T of the regularized image, with the transported form, has a class reached from [U] by m blowup steps (m = number of relative and centripetal steps). Chain forms: `relative_chain`, `special_chain`, `unary_chain` (Section 6's unary chains, used by 6.38). Steps: `SpecialChainRel.step_rel` (relative data; inactive labels split off, `SpecialChainSplit.clsG_split`), `SpecialChains.clsG_reg`/`clsG_zc` (regularization and zero-centred steps keep the class), `SpecialStep.step_of_data` (datum `datumOf`, R171 finite-to-one check `inactive_finite`). Pending: the partial-lift form (approved), to be stated with 7.13's head start for 7.14 |
| Lemma 7.12 | `blowup:same:RV:coa` | done on classes | `BlowupLiftGeneral.lemma_7_12` (every aperture datum, `liftCls [U^{τ,j}] = liftCls [U]` in K₊ μVF^◇[1+k]); `step_lift`, `steps_lift`, `muIsp_lift` (blowups of any length, μIsp). Construction: `BlowupLiftData.apertureData` (centres b₀, b₁), `BlowupLiftImage.mem_Vreg_iff` (image), `BlowupLiftContraction.lift_isomorphic` (μVF^◇ isomorphism onto the lift of the contraction), `BlowupLiftClasses.isoE`/`isoS`/`lemma_7_12_noInfinity`, `BlowupLiftGeneral.strict_annular` (∞ labels). Over the VF-generated base of Section 6. The object-level isomorphism is not stated separately (GAP-REPAIRS 7) |
| Lemma 7.13 | `kernel:dim:1:coa` | done (printed form, head start 0) | `KernelDimOne.lemma_7_13`: for A ≅ B in μVF^◇[1] and standard contractions (Section 6 `NormalizedMeasuredContraction`, head start 0), ([U], [V]) ∈ μIsp^db. Core form `KernelDimOne.lift_iso_muIsp`: 𝕃U ≅ 𝕃V in μVF^◇[1] for doubly bounded U, V ⇒ ([U], [V]) ∈ μIsp^db (6.38 on the composite, then `lemma_7_11` on both sides; `clsG_source`/`clsG_target`). Over the VF-generated base of Section 6, and over any substructure with support data V ⊆ T ⊆ acl(V) (`KernelBaseChange.lemma_7_13_of_support`, `lift_iso_muIsp_of_support`; e.g. `adjoin T b`, the base with adjoined VF parameters used in 7.15). The hypothesis [A] = [B] is read as A ≅ B (GAP-REPAIRS 1, 8). Pending: the approved head-start form, stated with 7.14 |
| Lemma 7.14 | `isp:VF:fiberwise:contract` | pending | |
| Corollary 7.15 | `contraction:same:perm:isp` | pending | |
| Definitions 7.16, 7.17, 7.19 | `rvaffine`, `defn:balance`, `def:units` | done (definitions) | `TwoCells.VAffine`, `RVAffine`/`HasSlope`, `Balanced`, `IsOneCell`, `PositioningCase`, `IsTwoCell` (geometric; definability imposed where used) |
| Remark 7.18 | `2cell:linear` | done (approved scope) | `TwoCells.paradigm_zero_iff`, `graph_of_zero` (∞-symmetry; A is the graph of f), `slope_eq` (s·t₁ = −t₂) |
| Lemmas 7.20–7.23 | `decom:into:2:units` … `contraction:perm:pair:isp` | pending | |
| Proposition 7.24 | `kernel:L` | pending | |
| Remark 7.25 | `thekernel` | pending | |
| Theorem 7.26 | `main:prop` | pending | |
| Corollary 7.27 | `db:to:novol` | pending | |
| Remark 7.28 | `eg:eb:factor` | pending | author: crucial. Assessed 2026-11-19 and reported: needs Section 3/4/6 bridges and the bounded RV decomposition; route awaiting author decision |

Corollary 6.37 on Section 7's classes: `ChartOfMeasured.liftCls_surjective`
(the converter `chartOf` reads a Section 6 measured RV object as a Section 4
chart; `RealBase.real_base` is the converse definability bridge).

Supporting modules: `BoundedClasses` (isomorphism classes of μRV^db[k] as a
commutative monoid, restriction and gluing of isomorphisms, refinement),
`RVMaps` (definability of RV maps and valuation comparisons), and the
Definition 6.34–6.37 chart lifts `MeasuredRVBridge`, `MeasuredRVBounds`,
`ChartLifting`, `ChartDiamondLift`.

Prepared for later results (supporting lemmas, not numbered results):
- `GoodPoints` (for 7.15, R126): a definable set of VF dimension < n lies in
  the zero locus of one nonzero polynomial over the base's VF parameter field
  (`exists_polynomial_vanishing_of_dim_lt`); a nonzero polynomial is nonzero
  at some point of a translated grid with more than its total degree points per
  side (`exists_grid_nonzero`, `exists_grid_nonzero_subfield`, Combinatorial
  Nullstellensatz).
- `SetBaseMatching`, `MeasuredLift`, `KernelBaseChange` (for 7.15): Lemma 6.38
  over support data (Section 6's proofs with upstream's without-field Lemma
  5.2); Lemma 7.11 from the lift of any doubly bounded measured RV object
  (`lemma_7_11_measured`); the adjoined base `adjoin T b` with
  `adjoin_support`, `adjoin_small`, `adjoin_gamma` (GAP-REPAIRS 9).
- `BaseExtension` (for 7.14, 7.15): for bases B ⊆ C, charts, isomorphisms,
  apertures and annular data over B extend to C with the same data; the
  extension of classes `clsExt` is additive and maps blowups to blowups and
  μIsp^db to μIsp^db (`step_ext`, `steps_ext`, `muIsp_ext`).
- `Groupification` (for 7.26): the Grothendieck group of M ⧸ c is K(M) modulo
  the differences of c-related elements (`groupQuotientEquiv`); no
  cancellation in M is assumed.
