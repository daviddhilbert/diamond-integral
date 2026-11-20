# Section 7 formalization plan

Status: **approved by the author on 2026-11-19**, with these answers to §5:

- **A.** Yes. The base is VF-generated, as set at the beginning of Section 6.
- **B.** Approved, except that 7.28 is crucial for applications. If 7.28
  cannot be formalized, report back instead of marking it "not pursued".
- **C.** Yes.

Implementation follows the milestones in §3.

Source: `section 2/reference/diamond_integral_revision_annotated.tex`, §7
(`section:int`, TeX lines 5299–5845). Numbers below are computed from the
current source (one shared counter per section) and agree with the labels
used in `HANDOFF.md` (7.14 = `isp:VF:fiberwise:contract`, 7.26 = `main:prop`).

## 0. Findings that change the starting point

1. **The manuscript side of §7 is already revised.** Definition 7.2 uses the
   bounded variable aperture τ with one bound Δ, the tagged shell/endpoint and
   the finite-to-one inactive projection. Remark 7.25 and Theorem 7.26 use
   J_var. Referee items R118–R137 and R171 are all marked resolved in the TeX.
   `HANDOFF.md` and `section 7/README.md` still say the main text has the old
   scalar 7.2 and 7.26; that is out of date. The remaining work is Lean.
2. **I checked every §7 statement and proof myself, before reading the
   referee notes.** I found no mathematical error in the revised text. §5
   lists the places where the Lean statement must be more general than the
   printed one, or where a choice is needed.
3. **The Def 7.2 and Notation 4.17 layer already exists in Section 4:**
   `AnnularBlowup`, `BlowupChart`, `BlowupRelation`, `RelativeAnnularGenerators`
   (`AnnularDatum`, `manuscriptIdeal` = J_var) and `RelativeAnnularConverse`.
   These modules were moved out of Section 7. `section 7/verification/status.json`
   still describes them as Section 7 components and records old pins. It is
   stale and will be regenerated.
4. **Generic confluence machinery is reusable.** hilbert-mathlib has
   `Rewriting/Iteration` (`Diamond`, `grid`, `Steps`, `Common`) and
   `Grading/GradedCongruence` (`congruence : RingCon (⨁ A i)`).
   integration_in_acvf's volume blowups (`S7/VolumeBlowupDiamond`,
   `IteratedVolumeRefinement`) are a line-by-line template for 7.5–7.10.
   The template's *structure* is copied; no upstream HK theorem is used as an
   input.

## 1. Representation decisions (implementation choices, not statement changes)

- **Base.** As in Sections 4 and 6: `T : LRV.Substructure M` with
  `VFGeneratedFieldBase T`. Section 4 objects are over `⟨(T : Set M), ∅⟩`.
  The STD hypotheses stay explicit: ACVF(0,0), IsCanonical, κ > ℵ₀, saturation,
  small base, `NontrivialDefinableGamma`. Final exports use the
  `_discharged` Section 6 twins, so `GammaPiecewiseRationalAffineInput` does
  not appear in them.
- **Γ names.** The paper's base is VF-generated, so every Γ-point definable over
  it is already a value of a base VF point. With Ξ = ∅, the Γ-named and raw
  categories therefore have the same objects. §7 does not consume upstream
  §7 (`GammaObjectAt`, `GammaVolumeObjects`), so I do not plan to introduce
  Γ-named categories here. **Question A** asks the author to confirm.
- **RV side.** Objects of μRV^db[k] are Section 4 bounded charts
  (`RVBoundedCharts.BoundedChart ⟨T,∅⟩ k`) with `NoInfinity`. Isomorphisms are
  `RVMeasuredCharts.Iso`, which preserve total weight (cond:mg2). This is where
  `AnnularDatum`, the blowup charts and J_var already live.
  `RVStrictBoundedComparison.equivalence` connects these charts to the ring that
  admits ∞ coordinates.
- **VF side.** μVF^◇[k] is Section 6 `DiamondCategory.VFObject` and `Morphism`,
  with `DiamondGrothendieck.KPlus/KGroup`. The lift is
  `DiamondLift.liftObject`; `DiamondLiftHomomorphism.liftHom` and
  `liftHom_surjective` give Corollary 6.37.
- **Bridge (new).** Section 6's `liftHom` is defined on
  `KPlus (rvPresentation T k)`, whose objects are `MeasuredRVObject`s. Section 7
  already has `toMeasured`/`measuredIso` from charts to those objects. I add the
  reverse converter and a degree-k semigroup equivalence between chart classes
  and `rvPresentation` classes, so each fact is proved once.
- **Fixed-degree K₊ μRV^db[k] (new).** This is the semigroup of isomorphism
  classes under the tagged ⊎. It is the carrier of μIsp^db[k] as an `AddCon`.
  Section 4 has only the whole-ring K₊.
- **Base change S → S⟨a⟩.** 7.14's hypothesis and the induction in 7.24(∗)
  live over S⟨a⟩. So μIsp is parameterised by the base substructure, and I
  need lemmas showing that adjoining a VF tuple preserves VF generation,
  smallness and nontrivial Γ.

## 2. Statement-by-statement plan

Legend: **Inputs** are checked Lean declarations to reuse; **New** is the
intended Lean statement; ⚑ marks a flag that is also listed in §5.

### 7.1 Notation `punc:RVd` — shell and endpoint
- **Route.** Definitional.
- **Inputs.** `AnnularBlowup.shellPoints`, `endpointPoints` (multiplicative Γ:
  `1 < codeValue s ≤ codeValue τ(u)`).
- **New.** Lemmas covering every finite γ ≥ 0: at depth zero the shell is empty
  and the endpoint is any t with vrv t = 0; neither part contains ∞; both are
  doubly bounded.

### 7.2 Definition `defn:blowup:coa` — apertures and annular blowups
- **Route.** Package the existing pieces.
- **Inputs.** `AnnularBlowup.Aperture`, `InactiveFinite`, `blownCoordinate`,
  `shell_finite_fibres`, `endpoint_finite_fibres`,
  `BlowupChart.shellChart`/`endpointChart`, `BlowupRelation.shellBounded`/
  `endpointBounded`, `RVTaggedCoproductProperties.boundedCoproduct`, and
  `RelativeAnnularGenerators.AnnularDatum.annularObject`.
- **New.**
  - `ElementaryBlowup U W`: an `AnnularDatum` D with source U, together with
    `Iso W D.annularObject`.
  - `Blowup V W`: finitely many disjoint subobjects C_i of V (restricted
    charts), sources U_i with isomorphisms U_i ≅ C_i and elementary blowups of
    U_i, and an `Iso W ((V ∖ C) ⊎ ⊎ U_i♭)`. Empty loci are allowed.
  - `IteratedBlowup n V W`: the chain of length n.
  - The bridge lemma "the elementary blowup *is* U^{τ,j}" is immediate from
    the definition.
- ⚑ Δ: Section 4's `Aperture.bound` is a Γ value without a definability
  requirement. The paper asks for a definable Δ. These agree for bounded
  objects by Remark 7.4, which is proved below. No Section 4 change is needed.

### 7.3 Remark (unlabelled) — infinite apertures excluded
- **Route.** Heuristic comparison with [Yin:int:acvf, Def 6.1].
- **New (optional).** If U has an elementary blowup then dim_RV U < k. The
  ordinary-blowup comparison is heuristic. ⚑ **Question B.**

### 7.4 Remark `db:blowup:bound`
- **Route.** (i) A blowup of a db object is db: `shell_domain_bounded`,
  `endpoint_domain_bounded`. (ii) For U ∈ μRV^db[k], every definable
  τ : U → RV has doubly bounded image (Lemma 2.41 `db:to:db`), and a bounded
  definable subset of Γ has a definable upper bound, so Δ can be named.
- **Inputs.** `MeasuredRVBounds.values_doublyBounded` (uses `lemma_2_41`), and
  the discharged 2.41 in `section 3/Section2GammaLinearityDischarged.lean`.
- **New.** `blowup_doublyBounded`, and
  `aperture_named_bound : ∃ Δ named over T, ∀ u, codeValue τ u ≤ Δ`. 7.14's
  descent uses the second.

### 7.5 Lemma `elementary:blowups:preserves:iso:vol`
- **Route.** As printed. Split U by γ_U ≤ γ_V∘F. Blow up the shallower
  endpoint with the ratio aperture τ_V∘F / τ_U. The comparison map is
  (u,s) ↦ (F u, s), (u,τ_U,s′) ↦ (F u, τ_U s′), endpoint ↦ endpoint.
  Total weights agree. The other side is symmetric, and an empty locus gives
  the identity.
- **Inputs.** Chart restriction and coproduct
  (`RVTaggedCoproduct*`, `RVMeasuredIsomorphisms.trans/symm`), and
  `rvMul_right_cancel`.
- **New.** `elementary_diamond : Iso U V → ElementaryBlowup U U₁ →
  ElementaryBlowup V V₁ → ∃ U₂ V₂, Blowup U₁ U₂ ∧ Blowup V₁ V₂ ∧ Nonempty (Iso U₂ V₂)`.
  The ratio aperture needs the finite-to-one condition on the endpoint
  subobject, which the paper verifies.

### 7.6 Corollary `eblowup:same:loci:iso`
- **Route.** Refine both loci into the pieces C_i ∩ F⁻¹D_l, apply 7.5 on each
  piece, transplant the remaining loci across F, and glue.
- **New.** `blowup_diamond` (one-step `Diamond` on isomorphism classes,
  mirroring upstream `S7/VolumeBlowupDiamond.volumeBlowup_diamond`).

### 7.7 Lemma `blowup:equi:class:coa` and 7.8 Corollary `blowup:equi:class`
- **Route.** `Iteration.grid` applied to the class-level diamond (7.7). 7.8 is
  7.7 with one length zero.
- **Inputs.** `HilbertMathlib…Iteration.{Steps, Diamond, grid}`.
- **New.** Exact length bookkeeping (n, m), with empty-locus padding.

### 7.9 Definition — μIsp^db[k], μIsp^db[*]
- **New.** `MuIsp T k U V : Prop := ∃ m n U′ V′, IteratedBlowup m U U′ ∧
  IteratedBlowup n V V′ ∧ Nonempty (Iso U′ V′)`. It descends to classes by 7.8.

### 7.10 Lemma `isp:congruence:vol`
- **Route.**
  - Equivalence relation: transitivity via 7.7.
  - Compatible with ⊎: blowups of a summand, padded.
  - Compatible with ×: a blowup times W is a blowup of U × W, using the
    pulled-back aperture. The finite-to-one condition and the bound survive.
- **Inputs.** `GradedCongruence.congruence`, and the
  `coprodRight`/`productRight` pattern (upstream S6 `AdditiveCongruence`,
  `ProductCongruence`).
- **New.** `muIspAddCon T k : AddCon (KPlusDB T k)` and
  `muIspRingCon : RingCon (⨁ k, KPlusDB T k)`.

### Before 7.11 — the object U_T
- **New.** For a special covariant bijection (a `RelativeApertureChain`) on
  𝕃U, U_T is the RV contraction of its image with the induced form
  (Γ-valued; R123). Inputs: `UnaryRelativeMeasuredMatching.sourceRV` and
  `BoundedVariableUnaryMatching.contractedMeasuredRVObject`.

### 7.11 Lemma `special:to:blowup:coa`
- **Route.**
  - Induction on the chain, with transport of blowups along isomorphisms.
  - Length 1: the locus is an RV-pullback, so restrict to it.
  - Finite-to-one check: λ(a,u) ∈ f_j(u)^♯ and λ(a,u) is algebraic over a
    (Lemma 2.13 `dcl:to:ac`), so finitely many f_j(u) lie over r (R171).
  - Then (u,s) ↦ (u, s f_j(u)) is an isomorphism U♭ ≅ U_T.
- **Inputs.** `RelativeApertureData` (`focusRV`, `endpoint`, `apertureBound`,
  `core`, `point`), `RelativeApertureChain`, `ScalarApertureInclusion` and
  `UnaryApertureInclusion` (regularization and old chains), and Lemma 2.13.
- **New.** ⚑ This is stated for a **partial lift**: U ∈ μRV^db[k], a set of
  lifted coordinates, and a chain acting on one of them. The printed statement
  is the special case of the full lift. 7.14 (Comparison step) uses the
  partial-lift form, as its text says. **Question C.**

- **Lean route (fixed 2026-11-19, after 7.12).** A tagged RV-pullback set A
  with finite fibres is the lift of its contraction C(A)
  (`preparedRVObject_lift_carrier`), and `ChartOfMeasured.chartOf` turns C(A)
  into a Section 4 chart. So the single relative step reuses the 7.12 pipeline:
  1. Generalize `BlowupLiftImage`/`BlowupLiftContraction`/`BlowupLiftClasses`
     from the specific centres to arbitrary `RelativeApertureData` on the lift,
     with hypotheses rv(focus) = f_j(u) (from `focusRV`) and
     rv(endpoint) = τ(u) f_j(u). 7.12 is then the instance `apertureData`.
  2. For given data R, the aperture τ(u) = rv(endpoint)/f_j(u) on the active
     labels (definable by descent to labels and `RealBase.real_base`). The
     named bound is R.apertureBound.
  3. The finite-to-one condition (R171): `scalarFocusImage_finite` over
     S ∪ {a} for a fixed inactive VF input a (Lemma 2.13 route), then finite
     fibres of A.
  4. Inactive labels map identically (tag rv(1)). Hence
     Step (cls (chartOf C(A))) (cls (chartOf C(reg R(A)))).
  5. Chains: induction, with regularization steps changing C(·) only up to
     isomorphism, and Lemma 7.7 to transport blowups.
  6. 6.38's chains end in prepared sets. Intermediate sets need
     regularization before the next relative step (`RelativeApertureData`
     requires a tagged source).
  - **Status (2026-11-19).** Done for the full lift
    (`SpecialChainInduction.lemma_7_11`, with `relative_chain`,
    `special_chain` and `unary_chain`). The invariant `Good` is an RV pullback
    with finite RV fibres and a label-constant form; its class is that of the
    contraction of its regularization. The partial-lift form remains (see
    7.13).

### 7.12 Lemma `blowup:same:RV:coa`
- **Route.**
  - Reduce to an elementary blowup: lift the F_i by 6.33.
  - Lift the finitary centre relation r ↦ {(f_j(u), τ(u) f_j(u))} by the
    continuous tuple form of 6.30, giving b₀ and b₁.
  - Φ = x − b₀ on the shell branch and x − b₀ + b₁ on the core branch, with
    the two tags.
  - Φ is clopen on each label branch, continuous and relatively unary. Lemmas
    6.7 and 6.8 make it a proper covariant homeomorphism. Its derivative is
    triangular with unit diagonal off a lower-dimensional set, and the forms
    are equal.
- **Inputs.** `lemma_6_30_tuple_vfGenerated` with
  `TupleFinitaryLift.continuousAt`, `lemma_6_7`, `lemma_6_8`, `lemma_6_9`,
  `DiamondLiftHomomorphism.lemma_6_33_diamond`, `ChartDiamondLift.chartObject`
  and `chart_isomorphic`, and `DiamondLift.liftObject`.
- **New.** `Blowup U W → Isomorphic G (chartObject U) (chartObject W)`, and
  likewise for `IteratedBlowup`. On classes:
  `liftCls (cls D.annularObject) = liftCls (cls D.source)` (`LiftClasses.liftCls`
  is done).
- **Lean pipeline (done 2026-11-19).**
  1. A = the carrier of the lift of the source (∞-free case).
  2. Section 6 `RelativeApertureData` on A, in coordinate j, with focus b₀ and
     endpoint b₁ from `lemma_6_30_tuple_vfGenerated`. The covariance field
     holds with α = vrv f_j(u) and β_i = vrv f_i(u), because the fibres are full
     RV polydiscs and b₀ ∈ f_j(u)^♯. The named bound Δ comes from Remark 7.4.
     (`BlowupLiftData`)
  3. Regularize the image (Section 6 `regularization`, a special covariant
     step). The regularized image is the RV pullback of the endpoint and shell
     labels. (`BlowupLiftImage.mem_Vreg_iff`)
  4. Contract (`contractedMeasuredRVObject`) to W. `remark_6_15` on the chain
     gives 𝕃U ≅ 𝕃W in μVF^◇, since the forms agree.
     (`BlowupLiftContraction.lift_isomorphic`)
  5. Split W by tag. The raw maps Fe, Fs give measured RV isomorphisms from
     the endpoint and shell charts onto the pieces.
     (`BlowupLiftClasses.isoE`, `isoS`, `lemma_7_12_noInfinity`)
  6. ∞ labels: the strict datum on `strictChart` has the same source and
     blowup classes (Lemma 7.5's comparison isomorphisms with equal depths).
     (`BlowupLiftGeneral.lemma_7_12`, `step_lift`, `muIsp_lift`)
- The graft step of the original plan was replaced by regularization, which
  records every leading term as a label.

### 7.13 Lemma `kernel:dim:1:coa`
- **Route.**
  - 𝕃U ≅ A ≅ B ≅ 𝕃V. Apply 6.38 to the composite μVF^◇[1]-morphism; this
    gives special covariant bijections on both sides and a μRV^db[1]
    isomorphism of the contractions.
  - Each contraction is a blowup by 7.11.
- **Inputs.** `DiamondSimultaneous.lemma_6_38_diamond_contractible` (it allows
  arbitrary retained RV fibres), `remark_6_28`, `StandardContraction`, and
  `NormalizedMeasuredContraction`.
- **New.** ⚑ Stated with a **head start**: one VF coordinate plus RV fibres of
  dimension k. The printed statement is k = 0. 7.14's Comparison step uses
  head start k. **Question C.**

- **Status (2026-11-19).** Done with head start 0: `KernelDimOne.lemma_7_13`
  (hypothesis A ≅ B in μVF^◇[1]; GAP-REPAIRS 8) and the core
  `lift_iso_muIsp`.
- **Head start: built by the Lemma 7.14 session** (2026-11-19), as
  `Lemma714Compare.lift_iso_muIsp_head` in `section 7/Lemma714Compare.lean`
  (degree 1+k, isomorphism of full lifts fixing the k lifted label
  coordinates); only the 7.14 proof uses it. Original note: Lemma 6.38 for a μVF^◇[1] morphism that
  preserves the selected labels π, with chains carried to the head-start
  bundles (Section 6 `rvHeadStartBundle`, `carryHeadStartBijection`) so that the
  full-lift 7.11 applies in grade 1+k, and the 6.38 isomorphism of contractions
  upgraded to the head-start objects.

### 7.14 Lemma `isp:VF:fiberwise:contract` — highest-risk item
- **Route.**
  - n > 1: restrict to fibres over S⟨b⟩, induct with head start k + 1.
  - n = 1, in four steps:
    1. *Uniform witnesses.* Compactness over first-order witness codes, then
       pack the witness into one definable row.
    2. *Freezing.* Lemma 6.16 plus FMT on a common invariance radius for the
       whole row.
    3. *Descent.* Glue over RV codes. Name the aperture bounds after descent,
       by 7.4.
    4. *Comparison.* Use 7.13 with head start, through 7.11.
- **Inputs.**
  - Section 6: `lemma_6_16`, `remark_6_20`, `proposition_6_19_vfGenerated`,
    and `FrozenRVWitnessDescent` (unary template certificate: witness
    quotient, protected membership, form freeze, validity transport).
  - Template for the uniformisation: upstream
    `IntegrationInACVF.Section6.FiniteRV.lemma_6_14_ordered` (ordinary
    blowups). It takes the fibrewise hypothesis for every selected label
    presentation over `B.real ∪ x` and concludes over B. I copy its
    architecture, not its theorem.
- **New.** Hypothesis `∀ a ∈ A, MuIsp (T⟨a⟩) k (fibre A′ a) (fibre A″ a)`.
  Conclusion `MuIsp T (n+k) (T̂σ A′) (R̂σ A″)` for **any** standard contractions
  T̂σ and R̂σ with the same σ.
- **Feasibility check (2026-11-19).** Upstream `lemma_6_14_ordered` uses exactly
  this route: semantic witness schemata (definable sets with natural-number
  bounds), promotion of pointwise witnesses over `B.real ∪ range x` to
  `B`-definable schemata (`gamma_tuple_parameter_promotion`), compactness
  (`gamma_finite_witnesses`, via `Saturated.definable_finite_subcover_tuple`),
  freezing by Section 5 preparation (`gamma_prepare_finite_rv_families`),
  recoding to RV keys, and Finset-induction gluing. The compactness core, tuple
  promotion and preparation are generic over `DefinableOverBase` and reusable
  here. The schemata, promotions and realisations are specific to their blowups
  and must be rewritten for annular blowups. Upstream size: about 7–8k lines in
  about 100 files.
- ⚑ Effort and risk: expressing "is a witness" first-order, for whole blowup
  chains with finite-fibre bounds, is the largest single piece of new
  infrastructure. If the upstream selected-presentation technique transfers,
  it is reused. Otherwise the plan needs a uniform-family lemma: pointwise
  S⟨a⟩-definable witnesses give one S-definable row, by saturation.

- **Formal statement (draft, 2026-11-19; needed under either option of the
  scope question).**
  - Objects: `A' : DefSet (rawMixedSpace n r') T` and `A''` (over r''), with
    Γ-forms ω', ω'' and head-start labels π' : Fin k → Fin r', π''. Fibres
    over (a, u ∘ π) are finite (as for Section 6's `headStartMeasuredObject`).
    They are not μVF^◇ objects (the RV fibres are infinite); their head-start
    bundles are.
  - Fibre classes: for a ∈ VFⁿ, the RV fibre {u | (a, u) ∈ A'} with volume
    u ↦ u ∘ π' and form ω'(a, ·) is a doubly bounded measured RV object over
    `adjoin T a` (`KernelBaseChange.adjoin`), with class in
    Cls (BT (adjoin T a)) k.
  - Hypothesis: the same VF projection, and for every a in it, the fibre
    classes are μIsp^db-related (equal when k = 0).
  - Conclusion: for standard contractions F', F'' (Section 6
    `NormalizedMeasuredContraction`, same order),
    ([F'.headStartMeasuredObject k π'], [F''.headStartMeasuredObject k π'']) ∈
    μIsp^db[n + k] over T.
  - Supporting pieces already in place: `adjoin` and its support data,
    `BaseExtension` (from `adjoin T b` to `adjoin T a` when b is a term in
    T, a), Section 6's parameter templates and promotion
    (`MixedSetParameterTemplate`, `exists_promoted_mixed_set_template`).

### 7.15 Corollary `contraction:same:perm:isp`
- **Route.**
  - Take the common base pr_{~i}. The bad set E (non-differentiability and
    measure failure) has VF-dimension < n, so the bad parameters B have
    dimension ≤ n − 2 and lie in Z(P) for a nonzero polynomial P over S.
  - Choose one radius δ for both objects and both first-stage contractions.
  - Grid {c₀,…,c_d} ⊂ VF(S) with v(c_l) > δ: this needs nontrivial Γ(S) and
    residue characteristic 0. The lexicographically first grid point
    b ∉ Z(P) is good and lies in dcl(S,a).
  - Apply 7.13 at b, then 7.14 with head start 1.
- **Inputs.** `Morphism.bad`/`measure` (μVF^◇ morphisms carry the bad set),
  `vfDim`, the Mathlib Combinatorial Nullstellensatz, and
  `NontrivialDefinableGamma`.
- **New.** As printed, with `F : Morphism G A′ A″` relatively unary in i.
- ⚑ I need a lemma "vfDim B < m ⇒ B ⊆ Z(P), P ≠ 0 over the base field". I
  have not yet found it; if absent, it is new and proved locally.

- **Lean plan (2026-11-19, on the 7.14 input `FiberwiseInput.Lemma714`).**
  - Statement: `A' A'' : VFObject T (m+1)`, `F : Morphism G A' A''` relatively
    unary in coordinate `i` (the other VF coordinates fixed), standard
    contractions `NormalizedMeasuredContraction A'.carrier A'.form e` and the
    same for `A''`, with `e (Fin.last m) = i`. Section 6's stages contract the
    last VF coordinate, so a program in order `e` contracts `e(last)` first; the
    paper's `σ(1) = i` is `e (Fin.last m) = i`. Conclusion: `IspRel` of the two
    head-start-0 contraction classes over T (support data for T).
  - `m = 0`: this is 7.13 (`KernelBaseChange.lemma_7_13_of_support`).
  - `m ≥ 1`, steps:
    1. **First stage and tail.** A `NormalizedMeasuredContraction` is a
       zero-centred normalization, a reindexing by `e`, and an ordered
       program `step T tail` (`OrderedStandardContractionProgram`); the stage
       `T` contracts the last coordinate (`StandardContractionStage`,
       `contracted`). Show: the stage's contracted set `A'₁` (m VF coordinates,
       with the stage's new label as head-start label, induced form) has the
       tail as a standard contraction, and the tail's head-start-1 object has
       the class of the full contraction's head-start-0 object. Needed again
       in 7.23 and 7.24.
    2. **Fibres.** For `a ∈ VFᵐ` in the common projection, the fibre of `A'₁`
       at `a` (`FibreObjects.fibreObject`, head start 1) is the contraction of
       the unary fibre `A'_a` over `adjoin T a` by the restricted stage; so
       `𝕃(fibre) ≅ A'_a` in μVF^◇[1] over `adjoin T a`.
    3. **Good points (R126).** The bad set of `F` has VF dimension `< m+1`, so
       its bad parameters lie in a zero locus `Z(P)` (`GoodPoints`). Choose one
       radius `δ` for `A'`, `A''` and both first-stage sets; a grid point
       `b = a + y` (`y` from the base field, `v(y) > δ`, Combinatorial
       Nullstellensatz) is outside `Z(P)`, in the same δ-polydisc as `a`, and
       a term in `T, a` (so `adjoin T b ⊆ adjoin T a`).
    4. **Fibrewise μIsp.** At `b`, `F_b : A'_b → A''_b` is a μVF^◇[1] morphism
       over `adjoin T b`; with step 2, `lift_iso_muIsp_of_support` gives μIsp of
       the fibre classes at `b`; δ-invariance identifies them with the fibres
       at `a`; `BaseExtension.muIsp_ext` moves them to `adjoin T a`.
    5. **Glue.** Apply `Lemma714` to `A'₁`, `A''₁` with head start 1 and the
       tails (step 1), then step 1's class identification.
  - **Done (2026-11-19)**, `Corollary715Fibres.corollary_7_15`. The
    normalization issue (GAP-REPAIRS 11) is handled by independence of the
    centre (7.14 with equal sets), a common centre, and grafting normalized
    contractions of the first-stage sets after the first stage. Steps 2–4 run at
    a good point b over S⟨b⟩: slices of the first stages and of the conjugated
    map `N'' ∘ F ∘ N'⁻¹` are morphisms of μVF^◇[1] (`FibreRestriction`); the
    lift of the fibre object is the target slice; Lemma 7.13 there, then the
    transfer to S⟨a⟩ through the definable closure (GAP-REPAIRS 12).
  - Size: comparable to upstream's `corollary_6_15_uncountable` minus its 6.14
    core; several thousand lines.

### 7.16 Definition `rvaffine`, 7.17 Definition `defn:balance`, 7.19 Definition `def:units`
- **New.** `VAffine`, `RVAffine` (slope t ∈ RV), `Balanced` (paradigms in
  RV_∞), `OneCell`, and `TwoCell` (positioning ε, paradigm t ∈ RV, three kinds),
  plus their parameterised forms.
- For proper invariant sets the "point" 1-cell and the ∞-paradigm graph case
  never occur (proper invariant sets have full VF dimension). The Lean
  definitions keep them anyway, to match the text.

### 7.18 Remark `2cell:linear`
- **New.** The two paradigms are ∞ together, and the slope is −t₂/t₁. Both are
  proved (R127/R128 corrections included). The torsor-line picture is
  explanatory. ⚑ **Question B.**

### 7.20 Lemma `decom:into:2:units` — second-highest risk
- **Route.**
  - Variation of [Yin:int:acvf, Lemma 4.8] with FMT at the exceptional discs.
  - Then the rv-affine refinement (R130): prepare the relation R_ε(x,β,t′);
    atomic subdiscs are rv-affine ([Yin:int:acvf, Lemma 3.18]); constancy on
    prepared discs plus slope rigidity give rv-affinity on each disc.
  - Balanced cells either stay balanced or become kind 2. I checked the
    ε(D) + t₂^♯ = ε(D) step.
- **Inputs.**
  - Upstream `IntegrationInACVF.Section4.lemma_4_8`
    (`TwoCellDecomposition.lean:59`). This is Yin's theorem, not HK, and an
    allowed upstream export, but its output is a Γ-RV map with
    `DefinableTwoCell` fibres, not a proper-covariant standard contraction. An
    adapter is needed.
  - Section 6 `RVLocalLinearity.at_named_radius`, `RVSubballSpecialization`,
    `RVLinearRadiusClosure.{SlopeAt, slope_unique, closed_above,
    on_ordinary_ball}`. These use upstream `FullBaseAtomicity.Base`, so a base
    bridge is needed.
  - `lemma_6_16`, `lemma_6_27`.
- **New.** For proper invariant A ⊆ VF² there is
  `T : StandardContraction A σ` with every fibre a `TwoCell`. Also the version
  uniform in retained RV labels, which 7.22 uses.
- The fibrewise remark after 7.20 (n ≥ 2, with R131 notation) is proved
  alongside.

### 7.21 Lemma `2:unit:contracted`
- **Route.**
  - Product case (constant ε, or kind 2): use the identity.
  - Balanced case: the translations (x − ε⁻¹(y), y) and (x, y − ε(x)) have
    empty core clauses.
  - ε : (A₁, 0) → (A₂, −γ) is a μVF^◇[1]-morphism; 6.38 gives ψ with
    Jac_Γ ψ = γ, and (u, t₂) ↦ (t₁, ψ u) has Jacobian 0.
- **Inputs.** `lemma_6_38_diamond_contractible`, `StandardContractionStage`,
  `OrderedStandardContractionProgram`.
- **New.** As printed.

### 7.22 Lemma `subset:partitioned:2:unit:contracted`
- **Route.**
  - Prepare ω (6.21 and Remark 6.20).
  - Apply 7.20 with labels retained; c(a) = (θ(a), T̂σ(a, θ a)).
  - A* = graph of c. Grafting is a morphism, as in 6.27.
  - Apply 7.21 uniformly in s. Since 6.38 accepts retained RV labels, this is
    one application rather than compactness.
- **Inputs.** `lemma_6_21_vfGenerated`, `remark_6_20`, the grafting map from
  the 6.27 proof (`StandardContractionExistence`), `isomorphic_equivalence`.
- **New.** As printed.

### 7.23 Lemma `contraction:perm:pair:isp`
- **Route.** Contract {i, j} first; fibres over a ∈ A_E. Apply 7.15 on both
  sides of the morphism A_a → B from 7.22 and 7.21, then 7.14 with head
  start 2.
- **New.** As printed. The phrase "by compactness" is not needed; a note only,
  no text change.

- **Lean plan for 7.21–7.23 (2026-11-19, on the 7.14 and 7.20 inputs).**
  - Orders. Section 6's order `e` contracts `x_{e(last)}` first. The paper's
    order 12 contracts `x₁` first (`e = swap`), and order 21 contracts `x₂`
    first (`e = 1`). Cells are read with base `x_{e 0}` and fibre
    coordinate `x_{e 1}` (`TwoCellInput.cellAt`).
  - 7.21, in the uniform form 7.22 needs. Take `X : VFObject T 2` over a
    substructure with support data, whose label fibres are 2-cells with uniform
    data `ε(s, ·)`, `t(s)`, `t₁(s)`, `kind(s)` (`TwoCellInput.CellWith`), and
    whose form is constant on label fibres. Then there are normalized contractions
    of orders 12 and 21 with equal head-start-0 classes. The printed 7.21 is the
    case of one label value. Steps:
    1. Kind pieces (definable by the input) partition `X`; contractions and
       classes are glued over the partition.
    2. Kinds 0 and 1 (product cells `D_s × (t(s)^♯ + c(s))`): the same
       translation and unary stages in either order (Section 6
       `shear_contraction_stage_of_bundle`, unary contractions). The identity is
       the isomorphism, because reordering the volume coordinates keeps the weight.
    3. Kind 2 (balanced): the shear stages `(x, y − ε(s, x))` and
       `(x − ε⁻¹(s, y), y)` (`TwoCellGeometry.balanced_mem_right/left`). Then
       Lemma 6.38 with `s` as a retained label applied to `ε : (A₁, 0) → (A₂, −γ)`
       gives `ψ` with `Jac_Γ ψ = γ`. The map `(u, t₂) ↦ (t₁, ψ u)` has Γ-Jacobian 0.
  - 7.22. Prepare `ω` (Section 6 `lemma_6_21_vfGenerated`, `remark_6_20`).
    Apply the 7.20 input to the graph of `θ` with labels retained. Graft
    `c = (θ, T̂_σ)` to get `A → A*`, relatively unary in both coordinates (the
    grafting maps of Section 6). Then apply 7.21 to `A*`.
  - 7.23. For `n = 2`, apply 7.15 on both sides of `A → A*`, which is relatively
    unary in both coordinates, and use 7.22. For `n > 2`, contract `{i, j}` first
    (`FirstStage` twice): the fibres over `a ∈ VF^{n−2}` are 2-dimensional, the
    case `n = 2` holds over `S⟨a⟩`, and Lemma 7.14 with head start 2 glues them.
    Use the centre independence and good points of 7.15 (`Corollary715`,
    `FibreInvariance`, `StageSlices`).

  - **7.21 build notes (2026-11-19).**
    - Done: `TwoCellGeometry` (both translations, at set level), `ChainStages`
      (Lemma 6.38's chains as stages: `sourceStage`, `targetStage`). The
      background `PullbackStages` builds the lift of a unary stage to a fibre
      product `D ×ᵤ E` with relabelled labels; it serves the product kinds and
      the second stages.
    - Translation stage, order 21, balanced cells, when `v(t) > v(rv of y)`:
      Section 6 `CentripetalData` on coordinate `y` with focus `ε(s, x)`. The
      coefficient `c` has `v(c) ≥ δ + γ`, where δ is the invariance radius and γ
      the VF bound, so the core clause never fires. Since fibres are δ-invariant,
      `v(t) ≤ δ`. Follow it by `regularize`, so that `rv(y − ε)` becomes a label.
      Then `shear_contraction_stage_of_bundle` applies: the relative condition
      and the same-label displacement hold because the displacement is `−ε(s, x)`,
      and the bundle holds by replacement in the last coordinate. When
      `v(t) = v(rv of y)`, the fibre is `t^♯` itself and the cell is a product.
    - Order 12: the same, with focus `ε⁻¹(s, y)` on coordinate `x`. The inverse
      of an rv-affine map is rv-affine.
    - Class comparison: `(u, t) ↦ (t₁, ψ u)` with Γ-Jacobian
      `γ + vrv(t₁) − vrv(t) = 0`, through `FirstStage.cls_labelObject_eq` and an
      RV relabelling.

  - **Status (2026-11-20).** 7.21 (uniform form), 7.22 and 7.23 for n = 2 are
    done on the 7.14 and 7.20 inputs (`Lemma723TwoFinal.lemma_7_23_n2`).
  - **Lean plan for 7.23, n > 2.** The plan mirrors the reduction for 7.15, with
    head start 2 instead of 1. Orders `σ₂ = σ₁ ∘ τ`, where `τ` swaps the last two
    positions, so that both contract `{i, j}` first.
    1. Common normalization: by the independence of the centre, take `F₁`, `F₂`
       with a common zero-centred normalization `D` (`exists_contraction_with`).
    2. Two graft steps: `cls F = cls(H, head start 1)` for `H` a contraction of
       the first-stage set (`cls_graftRest`). Then generalize `cls_graftRest` to
       head start `k`, and use the centre independence with head start `k`
       (7.14 with `A' = A''`, labels `π`), to reach `cls(K, head start 2)` for
       `K` a contraction of the second contracted set `B`.
    3. The two sets `B₁`, `B₂` have the same VF projection (the E-coordinates of
       `D(A)` in the common order).
    4. Lemma 7.14 with head start 2 on `B₁`, `B₂`. Its fibre hypothesis is
       proved at good points `b`, as in 7.15. There the two stages restrict to the
       slice (a standard contraction of the 2-dimensional fibre `A_b` over
       `S⟨b⟩` in each order); apply 7.23 for n = 2 over `S⟨b⟩` (support data via
       `KernelBaseChange.adjoin_support`). Carry the result to `a` by invariance
       of the fibre objects and `BaseExtension.Transfer.ofDcl`. This is the
       analog of `FibreInvariance`, `StageSlices`, `ConjugatedMaps` and
       `Corollary715Fibres` for two stages.
    The same fibrewise machinery, for general head start `k`, serves the adjacent
    swaps with `m ≥ 2` in 7.24.
  - **Status (2026-11-20, later).** 7.23 is done in every dimension,
    hypothesis-free (`Lemma723General.lemma_7_23`). Step 4 is
    `SliceContractions.fibre_ispRel_at`: at a good point the slice program is a
    normalized contraction of the prepared slice `Y'_b` in the order 1, and the
    slice program of the swapped order one in the order `swap 0 1`
    (`OrderedProgramContractions.ofContractionOrd`; the prepared set has no zero
    coordinate, so its normalization is trivial).

### 7.24 Proposition `kernel:L`
- **Route.**
  - k = 0: both sides are isomorphism.
  - "If": 7.12 together with 6.37.
  - "Only if": (∗) independence of contraction and order, by induction on k.
    The case σ = τ is 7.15 with the identity. Adjacent swaps: m = 1 is 7.23;
    m ≥ 2 uses a common first stage (6.27), the induction over S⟨a⟩, and 7.14
    with head start k − 1. Then apply 7.15 to each arrow of the relatively
    unary chain (R134/R135).
- **Inputs.** `Morphism.factor : UnaryFactorization`, `remark_6_28`,
  `lemma_6_27`, `liftHom`.
- **New.** `Isomorphic G (chartObject U) (chartObject V) ↔ MuIsp T k U V`, for
  every k, base-polymorphic (needed for the induction).
- **Status (2026-11-20).** Done, no hypothesis beyond the standing base, on the
  repaired Definition 6.34 (GAP-REPAIRS 16, 17):
  `Proposition724.proposition_7_24` (degree n+1), `Proposition724Zero` (degree 0,
  hypothesis-free). The route differs from "New" above: no
  `Isomorphic ↔ MuIsp` statement is needed; the contraction class modulo μIsp^db
  is an invariant of the scissor presentation of K₊ μVF^◇.

### 7.25 Remark `thekernel`
- **Status (2026-11-20).** `Theorem726.remark_7_25` (ker of the graded lift
  ring map = `manuscriptIdeal`), via the inverse ring map; final statement
  `remark_7_25_kernel`.
- **Route.**
  - Generators lie in the kernel (7.12).
  - Every blowup differs from its source by J_var
    (`BlowupRelation.blowup_mem_ideal`, `AnnularDatum.generator_eq`).
  - Products of generators are generators.
  - Kernel ⊆ J_var through surjectivity and 7.24, with no cancellation.
  - Constant apertures give (P_Γ) ⊆ J_var.
- **Inputs.** `RelativeAnnularGenerators.manuscriptIdeal`,
  `RelativeAnnularConverse.ideal_eq_manuscriptIdeal`,
  `RelativeAnnularScalar.radiusIdeal_le_manuscriptIdeal`,
  `VariableApertureMeasuredComparison.relation_formula`, `liftHom_surjective`.
- **New.** `RingHom.ker liftRing = manuscriptIdeal T` for the graded lift
  `RVBoundedRing.Ring ⟨T,∅⟩ →+* KGrade μVF^◇`. J_var stays independently
  defined; it is not defined as the kernel. The old scalar statements stay
  about I.

### 7.26 Theorem `main:prop`
- **Status (2026-11-20).** Done (final statements `Theorem726.theorem_7_26`,
  `theorem_7_26_graded`):
  `Proposition724.integralEquiv` (semigroup, degree n+1),
  `Proposition724Zero.integralZero_bijective` (degree 0),
  `Theorem726.integralRingEquiv` and `integralGraded` (ring, onto
  `RelativeAnnularQuotient.Ring`, homogeneous). K μVF^◇[*] is the ring
  presentation `DiamondRing.Ring`; products of morphisms in `DiamondProducts`.
- **Route.**
  - The semigroup isomorphism is the inverse of the map induced by 𝕃 (6.37
    surjective, 7.24 injective).
  - A general lemma: the Grothendieck group of M/c equals Groth(M)/⟨x − y :
    x c y⟩ (proved locally).
  - With 7.10 and 7.25 the subgroup is J_var, giving the graded ring
    isomorphism.
- **New.**
  - `KPlus μVF^◇[k] ≃+ (KPlusDB T k) ⧸ muIspAddCon`, with the stated
    characterisation.
  - `KGrade μVF^◇[*] ≃+* RelativeAnnularQuotient.Ring ⟨T,∅⟩` (= ggk μRV^db / J_var).
- ⚑ The graded ring ggk μVF^◇[*] (product from `DiamondProduct.VFObject.product`,
  plus a proof that the product of morphisms is a morphism) is new. Section 6
  has only the per-degree groups.

### 7.27 Corollary `db:to:novol` — diagram (diag-diamond-interpol)
- **Route.** Every integral of [A] is represented by a standard contraction
  of A.
- **Inputs.** ∫^μ: `theorem_3_22_measured_graded` and `_lift_class`. ∫:
  `gammaGroundUnmeasuredPositiveIntegral_characterization` with the proved
  `completed18GroundLiftInput`.
- **New.**
  - Ring maps `RelativeAnnularQuotient.Ring → RVMeasuredPQuotient.Ring` and
    `→ RVOrdinaryPNormalization.Ring`, both by `Ideal.Quotient.lift` from
    `functional_ideal_maps_into_p` and `manuscriptIdeal_le_forget_kernel`.
  - A lemma that `Section3RVRingEquivalences.measured` sends `pClass` to the
    Section 3 principal element.
  - Forgetful maps from K μVF^◇ to Section 3's `GammaGroundMeasuredVF…` and
    `GammaGroundVF…` rings.
  - Both squares commute.
- ⚑ The Section 3 integrals are over a `GammaGroundContext` base, and Section 6
  is over a raw VF-generated substructure. These contexts have never been
  identified (DEPENDENCY-AUDIT). An explicit context bridge is required.
  Through ∫, the corollary inherits the existing author-approved [18] §5/§6
  overlay boundary. No new input is planned.

### 7.28 Remark `eg:eb:factor`
- **Route.** By 6.37 every proper invariant A is 𝕃U with zero form; then
  apply μΨ and the defining conditions of E_g and E_b, inverting [A].
- **New (required).** The identity E_g(∫[A]) = E_b(∫[A])·[A]^{−n} in Section 4's
  rings. The author marked this remark crucial for applications (answer to
  Question B). If Section 4 lacks the E_g or [A]^{−1} infrastructure, report
  back before choosing a route.

## 3. Dependency order and milestones

| Milestone | Results | Risk | Main new infrastructure |
|---|---|---|---|
| M1 Blowups | 7.1, 7.2, 7.3, 7.4 | low | `ElementaryBlowup`, `Blowup`, `IteratedBlowup` on Section 4 charts; restriction to subobjects; transport along isomorphisms |
| M2 Congruence | 7.5–7.10 | low–medium | fixed-degree K₊ μRV^db[k]; class-level diamond; `muIspAddCon`/`RingCon` |
| M3 Lifts | 7.11, 7.12, 7.13 | medium–high | chart ↔ `MeasuredRVObject` class bridge; U_T; partial-lift 7.11; head-start 7.13 |
| M4 Descent | 7.14, 7.15 | **high** | base change S⟨a⟩; uniform witness rows; dimension → polynomial lemma |
| M5 Two cells | 7.16–7.23 | **high** | adapter from upstream 4.8 to proper-covariant standard contractions; rv-affine refinement; base bridge for `FullBaseAtomicity.Base` |
| M6 Kernel | 7.24–7.28 | medium | graded ring ggk μVF^◇; groupification lemma; Section 3 context bridge for 7.27 |

M1 → M2 → M3 → {M4, M5} → M6. M4 and M5 are independent once M3 is done.
Each milestone is committed separately with `section 7/verify.py` passing and
README, STATUS/COVERAGE and GAP-REPAIRS updated.

## 4. Verification and documentation

- Add each module to `lakefile.toml` roots and `section 7/Section.lean`. The
  root `DiamondIntegral.lean` already imports `«section 7».Section`.
- `verify.py` already audits complete public types and transitive axioms
  (only propext, Classical.choice and Quot.sound). I will extend it with:
  - a paper-target map: label → declaration;
  - a check that no Section 7 export takes `GammaPiecewiseRationalAffineInput`
    or any upstream HK declaration as a hypothesis.
- New docs: `section 7/STATUS.md`, `COVERAGE.md` and `GAP-REPAIRS.md`, in the
  Section 4/6 format. Also refresh `HANDOFF.md` §7, `DEPENDENCY-AUDIT.md` and
  `section 7/README.md`.
- Only complete numbered results are reported as such. Supporting lemmas and
  bridges are listed separately.

## 5. Flags and questions for the author

No mathematical error was found in the revised §7. The points needing a
decision:

- **A. Base convention.** Use the raw VF-generated base ⟨T, ∅⟩, as Sections 4
  and 6 do, and do not introduce Γ-named categories in §7. Justification:
  the base is VF-generated, so Γ-named and raw objects coincide, and §7 uses no
  upstream Γ-named result. *Recommended: yes.*
- **B. Remarks.** Proposed Lean scope:
  - 7.3: the dimension claim only; the ordinary-blowup comparison not pursued.
  - 7.18: ∞-symmetry and slope −t₂/t₁; the torsor line not pursued.
  - 7.28: formalized after M6. *Answer: required, crucial for applications;
    report back if blocked.*
- **C. Generalized statements.** Formalize 7.11 for partial lifts and 7.13
  with a head start, deriving the printed statements as special cases. The
  paper's proof of 7.14 already uses these forms in words. I would add one
  clarifying sentence to the TeX after 7.11 and 7.13, shown to you in a
  coloured review PDF first. *Recommended: Lean generalization yes; TeX
  sentence optional.*
- **D. Effort.** M4 (7.14 uniform witnesses) and M5 (7.20 two-cell
  decomposition) are each comparable in size to a full earlier section. No
  new cited input is planned for either. If the uniformisation proves
  infeasible to copy from upstream `lemma_6_14_ordered`, I will report before
  proposing any accepted input.
- **E. Smaller notes, no decision needed.**
  - Δ definability (§2, 7.2) is resolved by 7.4.
  - "by compactness" in 7.23 is superfluous.
  - `HANDOFF.md` and `section 7/README.md` say §7's text is unrevised; I will
    correct them.
  - `section 7/verification/status.json` is stale.
