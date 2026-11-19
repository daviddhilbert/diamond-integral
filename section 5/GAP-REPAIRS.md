

# Section 5 gap repairs

## Second audit (November 18): findings and triage

Author scope (README): omit the cross-section expansion and the [19]
computations; prove Lemma 5.12 and everything after it.

- To do:
  - (done) Theorem* Inflated-family Fubini (the approved R083–R085 proof):
    - `inflated_family_fubini` (`InflatedFamilyFubini.lean`): there is a
      finite base-definable partition (E_a) of Γⁿ with classes v_a such that
      E_b∫[A_γ] = v_a for every base-definable γ ∈ E_a (over ℂ((t)), the
      rational γ); the empty-fibre region has value 0; and
      E_b∫[A^inf] = gⁿ Σ_a χ_b(E_a) v_a, with the factor gⁿ retained.
    - `PuiseuxOriginal.inflated_family_fubini_vol` (`InflatedFamilyFubiniVol.lean`):
      Vol([A^inf]) = [G_m]ⁿ Σ_a χ_b(E_a) Θ(v_a), with
      `ambientPuiseuxComparison_nativeTorusClass` giving Θ(g) = 𝕃 − 1 = [G_m].
      `puiseux_inflated_family_fubini_vol` is the same statement in the
      constructed ambient.
    - Modules:
      - Track A (uniform representatives over Γ-parameters):
        `InflatedGamma{FamilyRows,CodePromotion,WeakLiftSchemata,UniformRepresentatives}`;
      - Track B (relative monomial decomposition, Smith reduction):
        `Inflated{IntegerBlockReduction,RelativeMonomialDecomposition,RelativeMonomialValues}`;
      - base partition: `InflatedGammaBasePartition`.
    - Proof-route deviation (statement unchanged): the base-partition step
      uses Section 4's Γ-Fubini (`integratePrefix`, `integrateAll_factor`)
      instead of the closed-polyhedra argument.
    - Axioms: propext, Classical.choice, Quot.sound.
  - (done) Theorem 5.17 and Proposition 5.23 for RV[*] fibres,
    `WeakDegreeFubiniDischarged.lean`:
    - `bounded_weak_fubini_discharged` wraps `nativeBoundedWeakVFFubini`
      with every input supplied;
    - `geometric_weak_fubini_discharged` is new: fibre representatives
      `U : NativeWeakRVObject … k`, `V` of degree l, with the value
      Σ over exact-degree strata, each normalized in its own degree;
    - checks that this is the paper's definition:
      `nativeWeakGeometricValue_eq_sum_strata`,
      `nativeWeakGeometricValue_toWeak`, `…FibreLiftEquality.toWeak`
      (the single-degree hypotheses imply the new ones), and
      `nativeGeometricVFFubini_via_weak`;
    - new argument: stratum-wise padding of zero labels by `𝔾_m ⊔ pt`
      (`thickAt`), which keeps the RV[*] row value and the geometric value
      of the lift family (E_g(∫(𝒪^× ⊔ (1+𝔪))) = 1), followed by
      compactness and a base partition, reducing to
      `native_vf_fixed_geometric_whole_witness_fubini`;
    - axioms: propext, Classical.choice, Quot.sound.
  - (done) Notation 5.15 Vol and Corollary 5.21 are no longer possibly
    vacuous. `PuiseuxMonsterAmbient.lean` contains:
    - `MonsterModels.exists_saturated_homogeneous_extension`: in ZFC, every
      L-structure has a κ-saturated, strongly κ-homogeneous elementary
      extension for regular κ. The construction iterates an ultrapower step
      along κ (Łoś realizes types and extends partial elementary maps),
      takes directed colimits of elementary embeddings, and gets
      homogeneity by back-and-forth. It uses only Mathlib.
    - `exists_puiseux_ambient`: an ambient for the concrete Puiseux model
      with exactly the binders of `corollary_global_vanishing_discharged`;
    - `PuiseuxAmbient` (inhabited), `puiseuxBoundedVFVolume` and
      `puiseux_corollary_global_vanishing`.
    - Axioms: propext, Classical.choice, Quot.sound.
  - (done) The ambient Θ is an isomorphism. `ElementaryRESExtensionData.lean`
    and `ElementaryRESExtension.lean` give:
    - `elementaryRESReducedExtension` (an explicit inverse of
      `elementaryRESReducedRestriction`) with both composites equal to the
      identity, and `elementaryRESReducedRestrictionEquiv`;
    - `eliminateRealGammaRES_bijective`;
    - `PuiseuxOriginal.ambientPuiseuxComparison_bijective` and
      `ambientPuiseuxComparisonEquiv : RESDimensionFreeReduction.Ring B ≃+*
      EquivariantVariety.ModifiedRing`, for every elementary ambient.
    - Axioms: propext, Classical.choice, Quot.sound.
    Independence of Vol from the ambient is not claimed by the paper (one
    fixed 𝕌).
  - (done) Lemma 5.19, `Lemma519Polynomial.lean`:
    - `lemma_5_19`: for finitely many polynomials with coefficients in
      VF(𝕊), there is a special bijection T with A♭ an RV-pullback and
      each `rv ∘ F_i ∘ T⁻¹` rv-contractible (`IsRVContractible`,
      Definition `defn:corr:cont`);
    - also `lemma_5_19_base_coefficients`;
    - it uses the same route as `prepare_finite_original_base_RV_predicates`.
  - (done) Test 5.20 for tuple parameters, `Test520Tuples.lean`:
    `test_5_20_tuples` proves `fromOrdinary [a] = fromOrdinary [b] ↔`
    a tuple fibre-family witness with terms `Z × α_1^♯ × ⋯ × α_n^♯` versus
    `Z × G_m^n`, in both directions; also
    `tuple_witness_iff_fibre_only_witness`. The factor order is `Z × α^♯`
    rather than the paper's `α^♯ × Z` (a coordinate permutation).
- Not pursued:
  - Remark 5.16 (polyhedral base pieces; the polyhedral facts the inflated
    Fubini proof needs will be proved there);
  - Remark 5.18's examples and its equality reformulation;
  - the global form of the (twist:C) formula, which is internal to the proof
    of 5.14.
- Records: paper-target-5-14.json, final-corollary-approval.json and
  geometric-fubini-approval.json are out of date, and verify.py hard-codes
  an empty "remaining" list. Updated November 18: README.md;
  paper-target-5-14.json, paper-target-5-17.json and status.json (only the
  strings that verify.py writes); reference/final-corollary-approval.json,
  geometric-fubini-approval.json, and `lean_status_current` in the R084–R085,
  R090–R091 and R094–R095 approvals. In verify.py only descriptive strings
  changed: the ambient-comparison and bounded-Fubini texts (the latter
  called the lifting input "accepted"), the `scope` and
  `complete_numbered_results` of status.json (now listing the
  inflated-family Fubini, weak-degree 5.17/5.23, the ambient, Θ, Lemma 5.19
  and Test 5.20, and the items not pursued), and the final message. The empty
  "remaining" lists are correct and were kept.

## Extraction (November 18)

The sixteen modules added above, with 18 Section 3 prerequisites, were
extracted into Fubini-theorems at `c94e50c` (source commit `d7117c9`) and
replaced here by compatibility imports recorded in `EXTRACTED-FOUNDATIONS.json`.
Fubini-theorems' public contract gained their 629 declarations, with full types
and axiom lists checked.
