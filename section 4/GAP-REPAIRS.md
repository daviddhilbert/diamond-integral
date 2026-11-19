# Section 4 gap repairs (from the numbered coverage audit)

Work in this checkout (`Section7/worktree/section 4/`), November 17, 2026, at
the author's instruction. Nothing is committed.

## Notation 4.17 / Lemma 4.18 — generator identification: repaired

Moved here from `section 7/` (they construct Notation 4.17's objects):
`AnnularBlowup.lean`, `BlowupChart.lean`, `BlowupRelation.lean` (namespaces now
`DiamondIntegral.Section4.*`; added to `verify.py`'s module list).

`RelativeAnnularGenerators.lean` (done):
- `AnnularDatum` (doubly bounded chart `U` of degree `1+k`, coordinate `j`
  with `pr_{~j}` finite-to-one, aperture `τ` with `0 ≤ vrv τ ≤ Δ`),
  `annularObject` = the separately tagged union of shell and endpoint
  (`boundedCoproduct`), `generator = [U^{τ,j}] - [U]`, `generator_eq`.
- `manuscriptIdeal` (span of all generators), `generator_mem_ideal`,
  `manuscriptIdeal_le : manuscriptIdeal ≤ FunctionalApertureCompatibility.ideal`.

- Lemma 4.18 for the manuscript ideal itself: `manuscriptIdeal_homogeneous`,
  `manuscriptIdeal_le_forget_kernel`, `manuscript_quotient_injective_on_degree_zero`,
  `manuscriptIdeal_maps_into_p`, `manuscript_section4_compatibility`, and
  `AnnularDatum.generator_eq_relation` (each generator is the relation of its
  datum's Section 4 presentation).

`RelativeAnnularConverse.lean` (done): for every implemented presentation `P`
(base `W`, aperture `τ`), the manuscript datum `datum P` is `U = W × (1)`
(`unitChart`, `unitIdx`, `unitAperture`, `unitChart_finite`,
`unitChart_bounded`); the source, endpoint and shell of its presentation are
isomorphic to those of `P` by dropping the unit coordinate (`sourceIso'`,
`endpointIso'`, `shellIso'`, through `graph_bij`, `annular_mem_iff`,
`annular_weight`), so `relation_eq_generator : P.relation = (datum P).generator`.
Hence `ideal_eq_manuscriptIdeal : FunctionalApertureCompatibility.ideal B =
manuscriptIdeal B`: the implemented ideal is exactly Notation 4.17's `J_var`,
and all its checked Lemma 4.18 results are results about `J_var`.

`RelativeAnnularScalar.lean` (done): Notation 4.17's last sentence. For an
admissible radius `γ` with lift `t`, `scalarDatum` (unit point, `j = 0`,
constant aperture `t`) has shell isomorphic to `boundedAnnulus γ`
(`scalarShellIso`) and endpoint isomorphic to `boundedPoint t`
(`scalarEndpointIso`), so `pGamma_eq_generator : P_γ = generator`, and
`radiusIdeal_le_manuscriptIdeal : I = (P_Γ) ⊆ J_var`.

## Remark 4.10 — positive tensor map: repaired

`PositiveChartPresentation.lean`: `ChartRelations` (isomorphisms, unit,
products, empty charts, scissors `[a]+[b]=[c]+[d]`) present a positive scissor
semiring `KPlus` (a formal empty object represents `0`; every empty chart is
identified with it by a scissor), with classes `cls`, the relation lemmas
`cls_iso`, `cls_unit`, `cls_product`, `cls_empty`, `cls_scissor`, and the
universal property `lift`, `lift_cls`, `hom_ext`. No subtraction is used.

`RVBoundedPositiveTensor.lean`: the positive semirings on the actual charts
and relations of this section's chart rings: `RESPositive` (measured RES),
`RVPositive` (doubly bounded measured RV), `GammaPositive` (doubly bounded
measured Γ), `FinitePositive` (finite Γ coefficients). The RES inclusion
`ofRES` and the Γ lift `sharp` respect all relations and agree on finite Γ
charts (`square`), giving
- `comparison : RESPositive ⊗[FinitePositive] GammaPositive →+* RVPositive`,
  `comparison (x ⊗ y) = ofRES x * sharp y` (`comparison_tmul`); on generators
  `[a] ⊗ [b] ↦ [ofRES a × b^♯]` (`comparison_charts`); also on the plain
  tensor over `ℕ` (`comparisonNat`);
- `comparison_toRing`: the ring-level comparison
  `RVBoundedBalancedTensor.comparison` agrees with it on positive classes
  (via `resToRing`, `gammaToRing`, `rvToRing`).
This is μΨ^db as stated (a homomorphism; no injectivity or surjectivity is
claimed, matching the remark).

## Proposition 3.18 kernel witness (added November 18; recorded under section 3)

New modules `GermJumps`, `GammaEndpointInvariant`, `Proposition318Witness`
and `Proposition318CubeRoots` prove that the coefficient-translation kernel of
the unmeasured Ψ of Proposition 3.18 is nontrivial. They sit here because they
use this section's finite-boundary theory of definable unary Γ sets
(`GammaFamilyBoundary`, `GammaBoundaryConstancy`). See
`section 3/GAP-REPAIRS.md` for the statements and hypotheses (including the
Reichstein–Youssin input of Remark 3.15). Axioms: propext, Classical.choice,
Quot.sound.

## Definition 4.9 — ∞ coordinates in μRV^db: convention recorded (November 18)

Second audit finding. The paper's Terminology "bounded" makes a set doubly
bounded when valim ⊆ [−γ, γ]ⁿ, which excludes ∞ coordinates. The Lean bound
`RVMeasuredBounds.DomainBounded` only constrains coordinates with
`NonzeroRV (u i)`, so a coordinate equal to `iRVZero` (the paper's ∞) is
unconstrained, and Lean's `RVBoundedRing.Ring` has more generators than the
paper's K μRV^db[*]. Lean's tagged coproduct (`RVTaggedCoproduct`) pads with
`iRVZero` tags. Also, Proposition 4.15 asserts μE^db(x) = φ(x) for every
x ∈ K μRES[*], which needs μRES ⊂ μRV^db. RES objects may have ∞ coordinates
(Notation `0coor`).

Author decision (November 18): keep Lean's convention as harmless bookkeeping,
record it, and prove the comparison. The argument: split a chart by its
∞-pattern (which coordinates are `iRVZero`); on each piece, delete those
coordinates. This is a definable bijection that changes neither `f` nor the
degree, and it gives a measured isomorphism (the transported form is
ω ∘ drop⁻¹). Each ∞-free piece is doubly bounded in the paper's sense. So
inclusion of the paper's ring into Lean's is a ring isomorphism (it sends each
chart class to its own class). Lean proves the isomorphism and its value on
classes (`equivalence`, `equivalence_objectClass`,
`equivalence_symm_objectClass`). Compatibility with the grading, P_γ, J_var
and Ẽ_b follows because these are defined by the same classes, but it is not
stated separately.

Lean: `RVStrictBoundedComparison.lean` (proved). It contains:
- `InfinityFree` and `StrictChart`: bounded charts with no `iRVZero`
  coordinate, which are exactly the paper's doubly bounded objects;
- `StrictRing B`: the same scissor presentation as `RVBoundedRing`
  (unit, product, iso, empty, scissor), but on strict charts only;
- `toBounded`, `fromBounded`, `to_from`, `from_to`, and
  `equivalence : StrictRing B ≃+* RVBoundedRing.Ring B` with
  `equivalence_objectClass`.

`fromBounded` sends a chart to the sum over its ∞-patterns p of the class of
the piece with the p-coordinates deleted (`strip`, an isomorphism by
`coordinateIso`). The iso law is proved by refining over pairs of patterns,
the product law by reindexing patterns of a product as pairs, and the scissor
law because the strip map is injective on a fixed pattern. Axioms: propext,
Classical.choice, Quot.sound.

## Propositions 4.7 and 4.15 — Γ-linearity input discharged (November 18)

`Section4GammaLinearityDischarged.lean`: `proposition_4_7_discharged` and
`proposition_4_15_discharged` are the statements of
`Section3LinkedRetractionStatements` with the unary Γ rational-affine input
supplied by `Section5.GammaQE.gamma_piecewise_rational_affine`, which is proved
from RV quantifier elimination with no hypotheses.

## Second audit triage (November 18)

- To do:
  - (done) `Section4LinkedRemarks.lean`: the diagram (edb:eb:com)
    (`diagram_edb_eb_com`), `boundedRetraction_res`,
    `boundedRetraction_surjective`, `geometricRetraction_range` and
    `normalized_retractions_distinct` (Remarks 4.4/4.16), instantiated with
    `Section3T001Integration.ordinary` and the discharged Γ-linearity
    input. They take no T001 presentation;
  - (checked, kept) `CharZero (ModelResidue M)` in the 3.18 witness files
    cannot be dropped from the binders: the Reichstein–Youssin hypothesis's
    type needs it on residue subfields. Callers supply it from `h00` via
    `Section7.residueField_charZero_of_model00`.
- Not pursued (explanatory remarks the paper does not use):
  - the unmeasured RV^db[k] ring and the inequality in Notation 4.13;
  - the isomorphism K μΓ[0] ≅ ℤ[Γ_def] in Remark 4.6;
  - the colimit description and the "[A] = 1 equalizes" part of Remark 4.4
    ("we shall not pursue this further");
  - the second paragraph of Remark 4.16 (an alternative the paper rejects);
  - Remark 4.10's first sentence (a restatement of Lemma 2.41).
- Records: COVERAGE claims a coproduct presentation for Definition 4.1 that
  is not built; it is missing rows for 4.17/4.18; counts and the R069 status
  are out of date. Updated November 18 (COVERAGE.md, STATUS.md, README.md,
  verification/CITED-INPUTS.md, verification/completion-boundary.json,
  reference/deferred-proposals/README.md). The summary strings hard-coded in
  `verify.py` (copied into `status.json`) still call the unary rational-affine
  input accepted background.
- Formerly open, resolved November 19 (see below): Remark 4.2's
  multivariate rational-affine input.

## Third audit fixes (November 18)

- Lemma 4.18 factorization clause with the Γ input discharged:
  `Section4LinkedRemarks.manuscript_section4_compatibility_discharged`.
- Still linkage-only (minor): Remark 4.8's alternative descent
  (`RVT001AlternativeDescent.evaluation`) and the unnormalized ordinary range
  clause take the T001 presentation as a parameter; they can be instantiated
  with `Section3T001Integration` as done for the other remarks.
- Definition 4.1's coproduct identification remains open, as recorded.
  Remark 4.2's multivariate rational-affine input was resolved on
  November 19 (next section).

## Multivariate rational-affine normal form (November 19)

- `Section3GammaAffineInput.Input B` is now the theorem
  `Section3GammaAffineDischarge.input B`, for every base `B` and every arity,
  using only `M ⊨ ACVF` (no ACVF(0,0), saturation, nontrivial Γ or HK input).
  Proof: the finitely many Γ names of `B` in the graph are abstracted to free
  Γ variables over the real base (`fullGamma_tuple_abstraction`); the
  resulting predicate has a flat RV literal normal form with coefficients in
  the real base (`GammaQEFlatNormalFormArity.gamma_flat_normal_form_arity`,
  the binary Section 5 argument with free arity). At each graph point, if no
  equal-value pair of active monomials had different output slopes, a small
  output perturbation would keep a true clause true
  (`GammaQEOutputSlopes.graph_has_critical_pair`), contradicting uniqueness
  of the output. Solving the equal-value relation gives one of finitely many
  branches. Its constant combines Γ values of flat coefficients, named over
  `B` because RV multiplication, inversion and the RV map are function
  symbols and VF polynomial values lie in the definable closure field
  (`GammaQECoefficientNames`), with integral powers of the Γ names of `B`.
- `Section4GammaAffineDischarged.lean`: `exists_partition_discharged`,
  `exists_common_discharged`, `exists_decomposition_discharged`,
  `decompositionDischarged`, `constructed_geometric_sum_discharged`,
  `geometric_sum_discharged`, `euler_characteristic_discharged`,
  `pieces_nonempty_discharged`, `dimensions_bounded_discharged`. The
  original statements are unchanged. `geometric_sum` and `sum_independent`
  never took the input.
- No special-transformations or integration-in-ACVF source was edited; the
  binary parser and perturbation lemmas were re-proved locally in arity-free
  form in `section 4`.
