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
| Lemma 7.14 | `isp:VF:fiberwise:contract` | **done** | `Lemma714Reduce.lemma714 : FiberwiseInput.Lemma714 M G` (the `Lemma714*` modules; proved in a separate session and merged at e9ac1fe0). It was a temporary input by the author decision of 2026-11-19 ("Input + parallel build"); `FiberwiseInput.Lemma714` keeps the statement. Fibre objects over S⟨a⟩: `FibreObjects.fibreObject`; μIsp^db in any degree: `FiberwiseInput.IspRel`. Head start: `Lemma714Compare.lift_iso_muIsp_head` |
| Corollary 7.15 | `contraction:same:perm:isp` | **done** | `Corollary715Fibres.corollary_7_15`: for a morphism F : A' → A'' of μVF^◇[n+2] over a substructure with support data, fixing every VF coordinate except i = e(last), and any standard contractions F', F'' of A', A'' in the order e, the head-start classes are μIsp^db-related; hypothesis-free form `ProvedResults.corollary_7_15` (the form with `h714` is kept). One VF coordinate is Lemma 7.13 (`KernelBaseChange.lemma_7_13_of_support`). Route (GAP-REPAIRS 11, 12): independence of the normalization centre from 7.14 with equal sets (`Corollary715.ispRel_same_set`); contractions with a common centre (`ContractionChoice`); first stage and rest (`FirstStage`); reduction to fibres (`Corollary715.reduction_7_15`); the fibre hypothesis at a good point b over S⟨b⟩ with Lemma 7.13, then transfer to S⟨a⟩ (`Corollary715Fibres.fibreHypothesis`) |
| Definitions 7.16, 7.17, 7.19 | `rvaffine`, `defn:balance`, `def:units` | done (definitions) | `TwoCells.VAffine`, `RVAffine`/`HasSlope`, `Balanced`, `IsOneCell`, `PositioningCase`, `IsTwoCell` (geometric; definability imposed where used) |
| Remark 7.18 | `2cell:linear` | done (approved scope) | `TwoCells.paradigm_zero_iff`, `graph_of_zero` (∞-symmetry; A is the graph of f), `slope_eq` (s·t₁ = −t₂) |
| Lemma 7.20 | `decom:into:2:units` | **done** | `Lemma720.lemma720 M G : TwoCellInput.Lemma720 M G` (the `Lemma720*` modules; proved in a separate session and merged at d14dcd0c). It was a temporary input by the author decision of 2026-11-19 ("Input + parallel build"); `TwoCellInput.Lemma720` keeps the statement: a proper invariant A ⊆ VF² × RVʳ (retained labels) has a standard contraction whose fibres `cellAt F s`, in normalized coordinates, are 2-cells with cell data uniform in s and definable over T (`UniformTwoCells`). Formal reading: GAP-REPAIRS 13 |
| Lemma 7.21 | `2:unit:contracted` | done, in the uniform form used by 7.22 | Product cells: `ProductCells.cls_product_orders` and `exists_product_orders`, for families of product cells over labels. Each order uses the same two unary stages pulled back, and the classes agree through a block swap of labels. Cells of kind 0 or 1 are products (`ProductKinds.product_of_kind`). Balanced cells: `BalancedPiece.cls_balanced_orders`. One order is the translation `(x, y − ε)` (`BalancedShearStages`), the other the translation `(x − ε⁻¹, y)` of the transposed cells (`BalancedMatching.swapInput`); each is followed by a chain of Lemma 6.38 pulled back (`BalancedMatching.exists_balanced_matching`, `BalancedOrders`). The classes agree along `proj⁻¹ ∘ ψ ∘ proj` (`MapClasses.cls_labelObject_map`), with vrv(lead ψz) + vrv(t₁) = vrv(lead z) + vrv(t) (R132) |
| Lemma 7.22 | `subset:partitioned:2:unit:contracted` | done | `ProvedResults.lemma_7_22` (from `Lemma723Two.lemma_7_22`) on the object `A*`, with the balanced piece supplied by `Lemma723TwoFinal.balancedOrders`. Objects: prepared labels (`Lemma722Objects.prepObject`, R133), normalized image (`normObject`), graft of the RV point (`Lemma722Cells.cellObject`; label fibres are cells, `cellOf_eq`). Pieces by kind: `LabelPieces`, `RestrictContractions.cls_headStart_zero_split`, `PieceCombination`. Formal reading: GAP-REPAIRS 14 |
| Lemma 7.23 | `contraction:perm:pair:isp` | done | All dimensions, hypothesis-free: `Lemma723General.lemma_7_23` (orders σ and σ ∘ τ, τ the swap of the last two positions). n = 2: `ProvedResults.lemma_7_23_n2` (from `Lemma723TwoFinal.lemma_7_23_n2`, via `Lemma723Two.chain_order`). n ≥ 3: `Lemma723General.lemma_7_23_succ` (on the 7.14 input; `lemma_7_23_succ_proved` discharges it). The reduction to the two-stage fibre hypothesis is `Lemma723Reduction.reduction_7_23` (two grafts, `HeadStartK`, `HeadStartFinite`, the 7.14 input with head start 2); good points: `FibreGood2.fibreHypothesis2_of_good`; at a good point b the two stages restrict to the two-dimensional slice of the prepared set (`TwoDimSlices`, `SliceStages`), give normalized contractions of the slice object in both orders (`OrderedProgramContractions.ofContractionOrd`), with the fibre classes as classes (`SliceContractions.cls_sliceMOC`), and 7.23 for n = 2 over `S⟨b⟩` relates them (`SliceContractions.fibre_ispRel_at`) |
| Proposition 7.24 | `kernel:L` | done (on the intermediate-forms input) | Degree n+1: `Proposition724.proposition_7_24` (`liftCls x = liftCls y ↔ IspRel x y`) and `proposition_7_24_muIsp` (degree 1+k, with `MuIsp`), taking only `hIF : IntermediateForms M G` (GAP-REPAIRS 16, author decision 2026-11-20: input + parallel build). Degree 0: `Proposition724Zero.proposition_7_24_zero`, hypothesis-free. Route: (∗) `OrderIndependence.star`; arrows `MorphismClasses.morphism_classRel` with `Corollary715Moves`; invariant of the scissor presentation `contractionInvariant` with `ScissorClasses` and `TautologicalLifts` (GAP-REPAIRS 15–17) |
| Remark 7.25 | `thekernel` | done (on the intermediate-forms input and the lift-of-products comparison, see STATUS) | `Theorem726.remark_7_25`: `RingHom.ker liftRing = manuscriptIdeal` (J_var). The first half (μIsp-related classes differ by J_var) is `RingClasses.ispRel_mem`. No cancellation in K₊ μRV^db is used |
| Theorem 7.26 | `main:prop` | done (on the intermediate-forms input and the lift-of-products comparison, see STATUS) | Semigroup part: `Proposition724.integralEquiv : K₊ μVF^◇[n+1] ≃+ K₊ μRV^db[n+1]/μIsp^db` with `integral_eq_iff` (∫⁺[A] = [U] ↔ [A] = μ𝕃[U]); degree 0: `Proposition724Zero.integralZero_bijective`, `integralZero_eq_iff`. Ring part: `Theorem726.integralRingEquiv : K μVF^◇[*] ≃+* K μRV^db[*]/J_var`, with K μVF^◇[*] the ring presentation `DiamondRing.Ring` |
| Corollary 7.27 | `db:to:novol` | pending | |
| Remark 7.28 | `eg:eb:factor` | done | `Remark728.remark_7_28` (degree n+1) and `remark_7_28_zero` (degree 0): for A ∈ μVF^◇ over the real part of a Section 3 ground context (strongly homogeneous, author decision 2026-11-19), 𝔼_g(∫[A]) = 𝔼_b(∫[A])·[𝔸]^{-n}, with ∫ = `nativeVFChartIntegral` (for any accepted lift input; its values on lifts are fixed). Route: standard contraction (`remark_6_28_exists`, `remark_6_28`), forgetful map to Section 3 (`forgetVF`, `forgetVF_iso`, `forgetVF_lift`, `forgetRV`, `labelsRV`), chart identification (`chart_ordinary_class`, `BaseExtension`), agreement of the two evaluations on doubly bounded classes (`boundedIndependence`, from Section 4's bounded RV decomposition `RVBoundedDecomposition.boundedEvaluation_geometric_eq_bounded`), normalization (Section 4 `RVT001BoundedFactor.geometric_eq_bounded_mul`). Hypotheses besides the context: the valuation compatibility, a nontrivial valuation on the context's field, nontrivial Γ over the raw base |

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
- `BaseExtension` (for 7.14, 7.15): when definability over B implies
  definability over C (`Transfer`: B ⊆ C, or the names of B in the definable
  closure of C), charts, isomorphisms, apertures and annular data over B extend
  to C with the same data; the extension of classes `clsExt` is additive and
  maps blowups to blowups and μIsp^db to μIsp^db (`step_ext`, `steps_ext`,
  `muIsp_ext`).
- Modules of the 7.15 proof, reusable for 7.14, 7.23 and 7.24: `FirstStage`
  (head-start class of a contraction = head-start-(k+1) class of its rest;
  shared with the 7.14 session), `ContractionChoice`, `Corollary715`,
  `FibreInvariance`, `FibreComparison`, `ConjugatedMaps`, `FibreRestriction`
  (restriction of a coordinate-fixing map to slices, as a morphism of
  μVF^◇[1] at good points).
- `Groupification` (for 7.26): the Grothendieck group of M ⧸ c is K(M) modulo
  the differences of c-related elements (`groupQuotientEquiv`); no
  cancellation in M is assumed.
