# Section 6 gap repairs (from the numbered coverage audit)

Source of findings: `verification/numbered-coverage-audit/COVERAGE.md` (on branch
`origin/codex/section6-gamma-kernel` only; not in this tree) (commit `ae379b3`, snapshot `f80d601`).
Work done in this checkout (`Section7/worktree/section 6/`), November 17, 2026,
at the author's instruction. Nothing is committed.

## Definition 6.34 (`defn:diamond`) — missing construction: built

`DiamondCategory.lean`
- `VFObject S n`: the objects of `μVF^◇[n]`: a definable carrier in
  `rawMixedSpace n labels`, a Gamma form, `ProperInvariant` carrier, finite RV
  fibres (objects of `μVF[n]`), and the form proper covariant in the sense of
  Definition 6.2 (`prop:pseu`): on each VF-fibre the form is invariant under
  balls of a `t`-definable radius (`formCovariant`).
  `VFObject.levelSet_geometry` recovers the manuscript's equivalent
  formulation (every level set is proper invariant).
- `IsStep`, `ObjectFactorization` (repaired 2026-11-20): a factorization
  inside `μVF^◇[n]`, i.e. a chain of steps between objects, each a relatively
  unary proper covariant homeomorphism that satisfies the measure identity on
  its own outside a definable set of VF-dimension `< n` (relative unarity is
  vacuous in degree zero). `UnaryFactorization` (homeomorphisms between
  definable sets) remains, as the forgetful image (`ObjectFactorization.toUnary`,
  `Morphism.factor`).
- `Morphism`: a bijection with a factorization inside `μVF^◇[n]` (`chain`) whose
  derivative satisfies the measure identity outside a definable set of
  VF-dimension `< n` (approved R102); in degree zero the exceptional set is
  empty, so morphisms preserve the form pointwise (empty Jacobian `1`).
  `Morphism.ofStep` builds a one-step morphism.
- `Isomorphic`, `Morphism.id`, `Isomorphic.refl`.

Design note (superseded 2026-11-20, author's decision "fix (1)"; manuscript
wording in review batch B10, pending the author's reading). The earlier note
read the intermediate sets as definable sets, not necessarily objects, because
requiring objects seemed "stricter than the text and not verifiable for Section
6's interpolation steps". Both reasons fail:
- The proof of Proposition 7.24 needs objects: it applies Corollary 7.15 to each
  factor ("a sequence of relatively unary μVF^◇[k]-morphisms, which exists by
  definition"), and 7.15 compares standard contractions of both ends. Without
  intermediate forms this breaks: `F(x, z) = (x, x·κ(z/x))`, with `κ` locally
  affine of slopes `1, t, 1/t`, is a relatively unary proper covariant
  homeomorphism of `𝔬²` whose target admits no covariant form making it
  measure-preserving, while `F⁻¹ ∘ F` is the identity (Section 7 GAP-REPAIRS 16).
- Every multi-step producer has unit derivative at VF-generic points on each
  step (checked by the parent session and here): special covariant chains
  (`SpecialCovariantChain.unit_derivative_of_independent`, per constructor),
  relative aperture chains, the retained unary chains with their `unit` field
  (the interpolation chains `vfInterpolation_unary_chain`,
  `ZeroCenteredData.relatively_unary_chain`, `headStartLift_unary_chain`), and
  Lemma 6.33's lift chains, whose steps are everywhere measured lifts between
  lifts of RV objects. So each intermediate set carries the transported form.
- `DiamondTransport` makes this precise: the transported form is proper
  covariant (`TransportedFormsLocal.locallyConstant_comp_inverse`,
  `TransportedFormsCov.covariant_of_locallyConstant`), the target has finite RV
  fibres (`TransportedFormsFibres.finite_rv_fibres`), and each step is
  measure-preserving (`transport_step`). These three files were proved by the
  session for the intermediate-forms input (branch `claude/intermediate-forms-proof`,
  commit 7b2b7ed2) and moved here.
- Rebuilt producers: `DiamondLift.liftChain_objects` (lift chains; `liftMorphism`
  now takes the standing hypotheses, for the proper invariance of the
  intermediate lifts), `DiamondSurjectivity.special_objects`,
  `DiamondSpecialIsomorphisms.relative_objects`, `DiamondTransport.retained_objects`,
  Remark 6.28 (`DiamondStandardContraction.remark_6_28`), `DiamondEmpty`,
  `DiamondLiftHomomorphism.zeroMorphism`, and the groupoid operations
  (`DiamondGroupoid.chain_inverse`, `step_inverse`, `ObjectFactorization.comp`).
  The final transported form is identified with the target's own form by an
  identity step (`id_step`, `id_step_generic`).

## Remark 6.35 (`dia:cat:well`) — missing groupoid proof: proved

`DiamondGroupoid.lean`
- `factor_inverse`, `homeo_inverse`, `unary_inverse`: factorizations invert.
- `Morphism.generic`, `morphism_of_generic`: the measure identity at
  VF-generic points is equivalent to the identity off a definable small set
  (via `exists_mixedGammaJacobian_exception`, `not_mem_small_set_of_independent`).
- `Morphism.inverse_nonempty`: inverses (generic derivative of the inverse and
  `mixedVFJacobian_inverse_product`).
- `Morphism.comp_nonempty`: composites (chain rule at generic points).
- `isomorphic_equivalence`: isomorphism is an equivalence relation in every
  degree, including zero.

## Corollary 6.37 (`L:sur:c`) — missing map and surjectivity: proved

Done:
- `DiamondGrothendieck.lean`: `emptyObject`, `restrictObject`, `complObject`,
  the positive scissor presentation `presentation` (Definition 3.1 instantiated),
  `KPlus`, `KGroup`, `vfClass`, `vfClass_iso`, `vfClass_empty`, `vfClass_scissor`.
- `DiamondEmpty.lean`: objects with empty carrier are isomorphic to the empty
  object in every degree; `vfClass_of_empty`.
- `DiamondProduct.lean`: products `μVF^◇[n] × μVF^◇[m] → μVF^◇[n+m]`
  (mixed product carrier, product form; proper invariance, uniform form
  covariance and finite RV fibres).
- `DiamondLift.lean`: `liftObject` (the lift of a measured RV object with
  proper invariant lift), `liftChain_factor`, `liftMorphism` (Section 6 lift
  chains with proper components are morphisms with empty exceptional set).
- `DiamondSurjectivity.lean`: `special_factor` (special covariant chains,
  including the zero-centred normalization through `RetainedUnaryHomeChain`,
  factor into relatively unary proper covariant homeomorphisms),
  `isomorphic_of_liftData`, `exists_isomorphic_lift` (degree `n+1`, over a
  VF-generated base, from Lemma 6.21 applied to the single piece) and
  `exists_isomorphic_lift_zero` (degree 0, from `lemma_6_21_zero_arity`):
  every object is isomorphic to `μL U` for a doubly bounded `U`.

- `DiamondLiftHomomorphism.lean`: `rvPresentation` (positive scissor
  presentation of doubly bounded measured RV objects: measured RV
  isomorphisms, restriction to a definable piece of the domain and its
  complement), `lift_isomorphic_zero` (degree 0, from the Lemma 6.31 zero-arity
  relabelling; `homeo_zero`), `lift_isomorphic_pos` (positive degree, from
  `lemma_6_33_doublyBounded_vfGenerated` and `liftMorphism`), `lift_restrict`
  and `lift_restrictCompl` (the lift of a restriction is the restriction of the
  lift, definitionally), `liftInvariant`, `liftHom : K_+ μRV^db[k] →+ K_+ μVF^◇[k]`,
  `liftHom_class`, and `liftHom_surjective`, for every `k ≥ 0` over a
  VF-generated base.

Scope: the base is VF-generated (`VFGeneratedFieldBase`), as in Section 6's
6.21 and 6.33 exports; the paper's Section 7 uses only this case.

## Lemmas 6.29, 6.33 — narrower degree: repaired

- `AllDegreeUnaryFactorizations.lean`: `RVUnaryFactorization`,
  `MeasuredRVUnaryFactorization` (a step's relative unarity is vacuous in
  degree zero), embeddings `ofChain`, `ofMeasuredChain` with equal composites,
  `lemma_6_29_all_degrees`, `lemma_6_29_measured_all_degrees` (every `k ≥ 0`;
  in degree zero every morphism, e.g. a swap of finite labels, is one step).
  Section 6's existing positive-degree exports are unchanged.
- `DiamondLiftHomomorphism.lean`: `zeroMorphism` and `lemma_6_33_diamond`:
  in every degree a measured RV isomorphism of doubly bounded objects over a
  VF-generated base lifts to a `μVF^◇` morphism compatible with the RV map on
  labels (degree zero: the 6.31 relabelling, a proper covariant homeomorphism
  by `homeo_zero`; positive degree: Section 6's lift chain).

## Lemma 6.38 — missing category bridge: repaired

`DiamondSimultaneous.lean`: `factor_homeo` (the composite of a factorization
from a proper invariant set is a proper covariant homeomorphism, Lemma 6.9),
`form_levels_open`, and `lemma_6_38_diamond`: for a morphism of `μVF^◇[1]` over
a VF-generated base, Section 6's matching export applies with its
homeomorphism, form-level and generic measure hypotheses discharged.

## Remark 6.15 (`spec:is:iso`) — missing bridge: repaired

`DiamondSpecialIsomorphisms.lean`: `relative_factor` (chains of the revised
Definition 6.11 class, `RelativeApertureChain`, factor into relatively unary
proper covariant homeomorphisms) and `remark_6_15`: such a chain between
objects of `μVF^◇[n]` with forms agreeing off a definable set of VF-dimension
`< n` (everywhere in degree zero) is a morphism of `μVF^◇[n]`.

## Lemma 6.21 / Remark 6.36 — passage to the category: repaired / recorded

6.21's object-level conclusion now passes to `μVF^◇` (`isomorphic_of_liftData`,
`exists_isomorphic_lift`, `exists_isomorphic_lift_zero`). Remark 6.36's proper
covariant discussion now has the category; its conjectural sentence is an
observation, not a claim to formalize.

## Remark 6.4 — missing implication: repaired, with a correction for the author

`ClosedSourceImageBounds.lean`: `remark_6_4` and `remark_6_4_properCovariant`.
For a source whose VF-fibres are closed, VF-bounded with doubly bounded RV
part, and the covariance clause of Definition 6.2 (`CovariantRadii`), the image
RV coordinates are doubly bounded. Proof: graph-fibre sources are open, so the
source fibres are clopen and the source is proper invariant (Lemma 6.5); then
the existing uniform label radius and Lemma 6.22 argument
(`target_rvBounded_of_open_nonzero_labels`).

Correction (approved by the author, November 17): the remark needs the image RV coordinates
to be nonzero, since "doubly bounded" excludes the value ∞. Counterexample to
the printed statement: `A = 𝒪 × {1}`, `f(a,1) = (a,0)`; all other conditions
hold (each VF-fibre is the identity of 𝒪) but `f(A)_RV = {0}`. The Lean
statement carries the nonzero hypothesis.

## Remark 6.32 (`rvdisc:stre`) — missing specialization: repaired

`RVDiscStretch.lean`: `remark_6_32`. For definable `a ∈ t^♯`, `b ∈ s^♯` and
definable `c ≠ 0` with `v(c) v(a) = v(b)`, the map `x ↦ b + c(x − a)` is a
definable bijection `rv(a)^♯ → rv(b)^♯` (`rvDiscSet`, `namedAffineMap`) with
derivative `c` at every point.

## Remark 6.28 (`stand:vol`) — category membership: repaired

`DiamondStandardContraction.lean`: `headStartSourceObject` (the head-start
object `A^♯` with its induced form is an object of `μVF^◇[(n+1)+k]`),
`remark_6_28` (a standard contraction induces an isomorphism of
`μVF^◇[(n+1)+k]` onto the lift `μ𝕃 T̂_σ(A)_{≤(n+1)+k}`: relatively unary chain,
unit derivative off a set of smaller VF-dimension, forms transported) and
`remark_6_28_exists` (standard contractions exist in every coordinate order
over a VF-generated base).

## Definition 6.11 — contracted layer: repaired

`ContractedApertures.lean`: `ContractedApertureData` (the RV-only aperture
data `τ`, `Δ`, focus, covariance), the centripetal transformation
`contractedPoint` (CT), `RelativeApertureData.toContracted` (aperture
`τ = rv(b/x₁)` read off a lift), `RelativeApertureData.point_contracts` (the
lift RV-contracts to CT), `ContractedApertureData.lift` and `lift_aperture`
(contracted data plus a continuous nonzero section `b` with `rv b = t_𝔭` is
lift data with the given aperture). So Lean's lift class is exactly the
manuscript's. The alternating grammar is `RelativeApertureChain` (whose
`original` steps include regularizations).

## Definition 6.24 — `(i, j)` relative unarity; μVF^◇ morphisms: repaired

`DiamondCategory.lean`: `VFRelativelyUnary f i j` (Definition 6.24, via
`Fin.cycleRange`), `vfRelativelyUnary_self` (the `(i, i)` case is
`VFUnaryRelativeAt`). The factorization step of `μVF^◇` morphisms now allows
any `(i, j)`, as Definition 6.34 does (an adjacent transposition of VF
coordinates is `(i+1, i)`-relatively unary). Inverses of `(i, j)` steps are
`(j, i)` steps (`unary_inverse`). All μVF^◇ constructions were updated;
sections 6 and 7 build. "Relatively special covariant" and Example 6.25 are
not used anywhere and are not formalized. Dropped by author decision on
2026-11-19 ("if it is not used then drop it"): the paper never uses the term
after Example 6.25.

## Lemma 6.16, Remark 6.17 — multi-dimensional extension dropped by author decision (decision recorded before 2026-11-19; date not preserved)

6.16 is the cited [Yin:special:trans, Theorem 5.5] (proved upstream). Its
statement is about a literal subset of VF, hence unary, and that statement
is formalized: `UnaryPreparation.lean: lemma_6_16` (full original-base
membership relation, arbitrary RV output arity). What was dropped is the
multi-dimensional extension, Remark 6.17 (every definable A). Both are used
only inside the proofs of 6.19/6.20, and 6.19 is checked in all arities.

## Lemma 6.30 (`RVlift`) in tuple arity: repaired

`TupleFinitaryLifting.lean`: `lemma_6_30_tuple`, `lemma_6_30_tuple_vfGenerated`.
For any definable finitary relation `R ⊆ U × RV^m` with `U ⊆ RV^N` (nonzero
coordinates; outputs may have zero coordinates) there is a definable center
function `c(a, v) ∈ VF^m` with `rv c(a, v) = v` whenever `R(rv a, v)`, whose
branch `a ↦ c(a, v)` is totally differentiable at every such `a`
(`TupleFinitaryLift`), hence continuous (`TupleFinitaryLift.continuousAt`).
This is the strengthened form (continuous, differentiable branches) used in
Section 7. Proof as in the manuscript, by induction on `dim_RV U`:
coordinate pieces with finite-to-one selected projections
(`RVCoordinatePieceCover.exists_cover`, `uniform_bound`), centers over the
selected VF coordinates with RV labels as parameters
(`exists_parametric_rv_centers`), the bad labels have smaller RV dimension
(`exists_small_rv_labels_for_tuple_differentiability`, point-rank criterion
`rvDim_le_iff_point_rank`), replacement over them by the inductive lift, and
gluing along RV conditions (`glue_lift`, `cover_lift`). Axioms: propext,
Classical.choice, Quot.sound.

## Remark 6.12 (`bigger:aper`): repaired

`ApertureIncrease.lean`. `ContractedApertureData.ApertureIncrease C` is a
strictly larger admissible aperture code `γ' > γ` on the same locus, focus
and labels; `target` is the resulting contracted data (Definition 6.11).
* `agree_outside`: outside the old core the two transformations agree;
* `old_core`: on the old core the new map gives either the new endpoint
  `t'_𝔭` (branch tag `true`) or the translated point `a - λ` in the released
  relative annulus `γ_𝔭 < v(a - λ) ≤ γ'_𝔭` (branch tag `false`), i.e. the
  image of the old core lies in `rv(𝔐_{γ_𝔭} ∖ 𝔐_{γ'_𝔭}) ⊎ {t'_𝔭}`;
* `released_attained`: every point of that annulus occurs over the fibre,
  because invariance (covariance radius `α ≤ γ_𝔭`) makes the whole old core
  present;
* `released_nonempty`, `endpoint_values`: the released part is nonempty and
  `vrv t_𝔭 = γ_𝔭 < γ'_𝔭 = vrv t'_𝔭`.
The comparison is fibrewise over the retained label `u`. Axioms: propext,
Classical.choice, Quot.sound.

## Remark 6.20 (`cons:extra`): VF-dimension one repaired

`UnaryRelationContraction.lean`, `remark_6_20_unary`. A proper covariant
`f : H → 𝒫(RV^q)` is given by its membership relation
`Rel ⊆ VF × RV^{r+q}`, and proper covariance is `ProperInvariant S Rel`
(bounded VF part, doubly bounded RV support, clopen membership sections), as
in the manuscript's definition for powerset-valued maps. For unary `H` (with
pieces and a Γ-form) the synchronized special covariant preparation can be
chosen with `f ∘ T⁻¹` rv-contractible: points with the same target RV
coordinates have the same membership row. As the remark says, the clause is
added to the induction: one radius makes all sections invariant
(`unaryRVDataRow_uniform_constant`, from `properInvariant_uniform_named_radius`
applied to `Rel` with its extra tags), finitely many obstacles control all
sections (`exists_unary_obstacles` applied to `Rel`), and the value-prepared
unary process carries the row through every focus step. Axioms: propext,
Classical.choice, Quot.sound.

Downstream: Lemma 7.22 (R133) uses only the Γ-valued instance, Lemma 6.21
(checked); Lemma 7.20 prepares a unary relation with FMT freezing, which is
`measured_frozen_unary_rv_data_preparation` (checked).

## Γ-linearity input discharged across Section 6 (November 18)

`Section6GammaLinearityDischarged.lean`. Forty-three numbered statements took
`GammaPiecewiseRationalAffineInput` as an explicit hypothesis: 6.4, 6.8, 6.9,
6.14, 6.15, 6.19, 6.20 (n = 1 and every n), 6.21, 6.22, 6.23, 6.27, 6.28, 6.33
and 6.38, in all their variants, including the contractible 6.38 versions
(first recorded as forty; the file now has 43 `_discharged` theorems). Each
now has a `_discharged` version: the same statement
without that argument, which is supplied by
`Section5.GammaQE.gamma_piecewise_rational_affine`. Where a conclusion
mentions the input (Remark 6.28), it is instantiated by that theorem.

## Lemma 6.29 — doubly bounded variants in degree 0 (November 18)

`AllDegreeDoublyBoundedFactorizations.lean`:
`lemma_6_29_doublyBounded_all_degrees` and
`lemma_6_29_measured_doublyBounded_all_degrees` cover every degree k ≥ 0. In
degree 0 the one-step factorization has only the two given objects as
intermediate objects. Before this, the 6.29 repair covered only 2 of the 4
variants.

## Second audit triage (November 18)

- To do:
  - (done) Lemma 6.38:
    - `UnaryRelativeMeasuredMatching` now has the fields
      `sourceContractible` and `targetContractible` (ω′ and σ′ are constant
      on equal RV coordinates). They are filled in by both existence proofs
      and preserved by `precompose`.
    - `BoundedVariableUnaryMatching.lean`:
      - `preparedRVVolume_finiteFibres` (the degree-1 projection is
        finite-to-one when RV fibres are finite);
      - `sourceRV` and `targetRV` (objects of μRV^db[1]);
      - `measuredRVIso` (the induced μRV^db[1] isomorphism; the balance
        condition comes from the volume identity);
      - `lemma_6_38_bounded_variable_apertures_contractible`, which adds
        `hFinite` (finite RV fibres: the paper's VF[1] condition, passed to
        A♭ and B♭ by Lemma `RV:fiber:dim:same`).
    - `DiamondSimultaneous.lean`: `lemma_6_38_diamond_contractible`, with no
      extra hypothesis (it uses `A.finiteRV`).
    - Axioms: propext, Classical.choice, Quot.sound.
  - (done) Remark 6.35, `DiamondGroupoidMaps.lean`: `Morphism.comp_exists`
    (map `H.map.comp F.map`), `Morphism.inverse_exists` (map
    `F.map.inverse _`), `IsMorphismMap` with `.comp`/`.inverse`, and a
    `CategoryTheory.Groupoid` instance on `DiamondObj` (objects of
    `μVF^◇[n]` in a fixed `DiamondContext`) whose morphisms are the
    underlying maps of Definition 6.34 morphisms;
  - Remark 6.20 for n = 1: covered by the general 6.20 assembly.
- Not pursued:
  - Remark 6.28's head start with infinite RV fibres at the μVF^◇ level;
  - Remark 6.15 for general μgVF forms (6.21 uses
    `measure_identity_ae` instead);
  - the cited [18, Lemma 5.6] claim in 6.36 (unused).
- Records: `Section.lean`'s closing docstring is out of date; 6.16 is marked
  "dropped" but `lemma_6_16` (unary) is formalized. Updated November 18:
  the 6.16 entry above and README.md. Known and left as is (records-only
  pass, no `.lean` or `verify.py` edits): the closing docstring of
  `Section.lean` still says 6.29 holds only in positive degree, that the
  Gamma affine background is retained, and that the main aperture
  definitions are not applied, and omits μVF^◇, 6.20 in all dimensions and
  the discharged versions; the `scope` string hard-coded in `verify.py`
  (copied into `status.json`) likewise says 6.29 and 6.33 hold "in every
  positive degree".

## Remark 6.20 (`cons:extra`) in every VF-dimension: repaired (November 18)

`Remark620.lean`: `remark_6_20`. The hypotheses are those of Proposition 6.19
(VF-dimension n + 1, A proper invariant and an RV-pullback, pieces P_i),
together with the membership relation `Rel ⊆ VF^{n+1} × RV^{r+q}` of a proper
covariant `f : A → 𝒫(RV^q)`, as in the text after Definition 6.2:
`ProperInvariant S Rel`, i.e. the RV-support is doubly bounded and every
membership section is proper invariant. The conclusion is that of 6.19, plus
rv-contractibility of `f ∘ T⁻¹`: `(T p).2 = (T z).2 → rvDataRow Rel p =
rvDataRow Rel z`. Axioms: propext, Classical.choice, Quot.sound.
`remark_6_20_discharged` (in `Section6GammaLinearityDischarged.lean`) also
drops the Γ-linearity input.

Method. The relation's rows are carried through the measured preparation as
a row form (`RowForms.lean`: `RowFormOn A q`, with a definable marked
membership graph, pullback, descent and extension). The form layer of the
measured preparation is mirrored in the 143 `Row*.lean` modules (plus `RowForms.lean`, 144 files in all) (mechanically
translated, then hand-repaired where the row form differs). Points to note:
- Domain marker: the membership graph of a row form also contains a marker
  tuple (all `0`) at each point of the domain. The row bound excludes the
  marker from rows, so first-order loci can quantify over the domain. The
  transition and core constancy loci (`RowGammaTransitionParameterLoci`,
  `RowGammaCoreParameterLoci`) are exact via `…_iff_row`.
- Prefix removal (`RowMeasuredProgramPrefixLoci`): the constancy locus of a
  composite transition is contained in that of the remaining transition.
  Only this direction is used downstream; equality would need the
  transition graph to be functional, which raw templates need not be.
- Rows are padded by a constant coordinate `1` (`paddedRow`), so that there
  is always a row coordinate for the marker (q = 0 included).
- Level sets of the row form are open, by the uniform radius of `Rel`
  (`properInvariant_uniform_named_radius`).
The top-level row result is
`measured_form_compatible_preparation_all_dimensions_row`, mirroring
`measured_form_compatible_preparation_all_dimensions`.

## Third audit fixes (November 18)

- Lemma 6.29 for RV[k] in every degree keeping finite volumes:
  `lemma_6_29_finiteVolume_all_degrees` (`AllDegreeDoublyBoundedFactorizations.lean`).
  `lemma_6_29_all_degrees` alone drops the finite-volume conclusion.
- Corollary 6.37 with the Γ input discharged: `liftHom_surjective_discharged`
  (`DiamondLiftDischarged.lean`).
- Degree-0 case of 6.33's first clause for non-doubly-bounded objects:
  done November 19, `AllDegreeMeasuredLifts.lean`: `lemma_6_33_zero_degree`
  (from `lemma_6_31_zero_arity`) and `lemma_6_33_all_degrees_vfGenerated`
  (every `k ≥ 0`, arbitrary objects: an everywhere measured lift exists; in
  positive degree it is the composite of a relatively unary chain with the
  given RV map, doubly bounded when both objects are).

## Still open in Section 6

(nothing beyond the "Not pursued" items of the triage above)
