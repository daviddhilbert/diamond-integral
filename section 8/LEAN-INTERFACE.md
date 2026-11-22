# Lean interfaces that Section 8 builds on

Survey of 2026-11-20 (read-only; signatures copied from the sources, not re-checked by compiling unless noted).
Paths: `EUL` = `.lake/packages/fubini_theorems/FubiniTheorems/Prerequisites/Euler`,
`F` = `.lake/packages/fubini_theorems/FubiniTheorems`,
`H` = `.lake/packages/hilbert-mathlib/HilbertMathlib/Foundation/Series`,
`ST` = `.lake/packages/special_transformations`.
Most files of `section 4` and all of `section 5` are one-line imports of these packages.

Standing variables: `{M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]`. One-sorted model: `iVF`, `iRV`,
`iRVMul`, `iRVZero`, `iRVOne`; `NonzeroRV x := iRV x ∧ x ≠ iRVZero`. Γ is **multiplicative**:
`Values.Gamma (M := M)` (`ST/Section3/ValueQuotient.lean`), `codeValue : M → Values.Gamma` (1 on zero),
`codeValue_mul`. "0 ≤ vrv" reads `1 ≤ codeValue`.

## The ring K μRV^db[*] and its universal property

- Base: `GammaParameters.Base` = `{real : Set M, gamma : Set Values.Gamma}`; `DefinableOverBase B sorts A`;
  `GammaDefinableClosureAtBase B γ`. Section 7 base: `BT T = ⟨(T : Set M), ∅⟩` (`section 7/LiftClasses.lean:84`).
- `RVMeasuredCharts.Chart B k` (`EUL/RVMeasuredCharts.lean:32`): `arity`, `domain : Set (Fin arity → M)`,
  `coordinate` (structural map), `volume`, definability and finite-fibre fields.
  `Chart.correctedWeight a u = a.volume u * ∏ i, codeValue (a.coordinate u i)` is ω_f.
  `Iso a b`: `equiv : a.domain ≃ b.domain`, `graph_definable`, `weight_eq`.
  `RESChart B k extends Chart` with `finite_values`.
- `RVBoundedCharts.BoundedChart B k extends Chart` with `domain_bounded : DomainBounded toChart`
  (bounds the labels). `product a b : BoundedChart B (l + k)`. Section 7: `Obj B k`.
- `RVBoundedRing.Ring B` (`EUL/RVBoundedRing.lean:46`), `objectClass a`, relations
  unit / product / iso / empty / scissor; `hom_ext` (`EUL/RVBoundedGrading.lean:23`).
- Universal property, direct: `RVBoundedRing.Invariant B R` (fields `value, unit, product, iso, empty,
  scissor`), `RVBoundedRing.lift B f : Ring B →+* R`, `lift_objectClass`.
- Universal property, disjoint unions: `RVFamilyDisjointPresentation.Invariant (family B) R` (fields
  `value, iso, coproduct, unit, product, empty`), `lift`, then compose with
  `RVBoundedDisjointPresentation.fromChartRing B`. Worked example: `section 7/Theorem726.lean:139–173`
  (`liftInvariant`, `liftRing`, `liftRing_objectClass`).
- Tagged coproduct: `RVTaggedCoproductProperties.boundedCoproduct`, `bounded_coproduct_class`.
- Restriction of a chart to a definable subset: `RVChartRestrictions.restrict a I hI hsub`.

## J_var

- `AnnularBlowup.Aperture r` (`section 4/AnnularBlowup.lean:54`): `aperture`, `graph_definable`, `nonzero`,
  `nonnegative`, `bound`, `bounded`. `shellPoints`, `endpointPoints`, `blownCoordinate`.
- `BlowupChart.shellChart`, `endpointChart` (`section 4/BlowupChart.lean`); `BlowupRelation.shellBounded`,
  `endpointBounded`, `sourceBounded`, `shell_weight` (weight of the shell = weight of the source times
  `codeValue s`); the endpoint weight is the source weight times `codeValue (τ u)`.
- `RelativeAnnularGenerators.AnnularDatum B k`, `.source`, `.annularObject`, `.generator`,
  `generator_eq` (= shell + endpoint − source), `manuscriptIdeal B`,
  `manuscriptIdeal_le_forget_kernel`, `manuscript_section4_compatibility` (𝔼_b kills J_var).
- Pattern for an inclusion generator by generator: `Theorem726.ideal_le_ker`
  (`Ideal.span_le.mpr`, `rintro _ ⟨k, D, rfl⟩`).
- `Theorem726.theorem_7_26 : KVF … ≃+* QRV T`, `QRV T = RVBoundedRing.Ring (BT T) ⧸ manuscriptIdeal (BT T)`,
  `intQ_lift`, `integralRing_ringClass`, `remark_7_25_kernel`. Hypotheses: `G` with `Valued (VF M) G`, `h00`,
  `hc`, `hκ : ℵ₀ < κ`, `hs`, `hv`, `T`, `hsmall`, `hΓ`, `B₀ : VFGeneratedFieldBase T`, `hntB`.

## RES rings and 𝔼

- `RESOrdinaryRing.Ring B`, `RESOrdinaryReduction.ReducedRing B` (quotient by `[α^♯] − [torus]`),
  `torusClass`, `fibre_class`. Degree-free: `RESDimensionFreeRing.Ring B`,
  `RESDimensionFreeReduction.Ring B` (this is the source of Θ), `fromGradedReduced`.
- `RVT001OrdinaryDescent.boundedEvaluation … kind : RVBoundedRing.Ring B →+* ReducedRing B`,
  `boundedEvaluation_res`; `RelativeAnnularQuotient.evaluation`, `evaluation_res`.
- Class of a literal RES set: `resSetClass hc A hA : RESDimensionFreeRing.Ring (EmptyGammaGround.base S)`
  (`F/Fubini/NativeRESClasses.lean:80`), `resSetClass_bijection`.
- Nearest statement to (twist:C): `RVOrdinaryBalancedTensor.evaluation_gamma_chart`,
  `nativeRVEvaluation_gamma` (value on `x ⊗ [I]` = `x · χ(I) · torus^n`). No global (twist:C) statement.

## Puiseux setting and Θ

- Concrete model: `Carrier = PuiseuxSeries ℂ ⊕ RV`, `RV = Option (RationalRVUnits ℂ)`,
  `RationalRVUnits k = Multiplicative ℚ × kˣ`; `canonicalInterpret`, `canonical_model_ACVF`;
  `baseCarrier` (the base ℂ((t)): Laurent series, and RV units of integer value);
  `originalPuiseuxGround`; `gammaNormalEquiv : GammaTop ≃ WithTop ℚ`, `rationalGamma`, `gammaRational`;
  `rationalGamma_definable q` (every rational value is definable over the base, concrete model).
- Ambient: `PuiseuxAmbient` (`N`, `e : Carrier ↪ₑ[LRV] N`, `G : GammaGroundContext N`, `hc`, `hB`, `hγ`),
  `puiseuxAmbient_nonempty`; `G.base.gamma` is the value group of ℂ((t)) (≅ ℤ), not ℚ;
  `ambientLaurentField_nontrivial`.
- `GammaGroundContext M`: `model00, κ, uncountable, saturated, homogeneous, real, fieldBase, gamma,
  values_mem, small_real, small_gamma, nontrivial_gamma`; `.base = ⟨real, gamma⟩`.
- Θ: `theta_5_14_concrete : RESDimensionFreeReduction.Ring originalPuiseuxGround ≃+* EquivariantVariety.ModifiedRing`;
  ambient: `ambientPuiseuxComparisonEquiv hcN e B hB hγ : RESDimensionFreeReduction.Ring B ≃+* ModifiedRing`.
  Classes: `modifiedAffineLineClass` (𝕃), `modifiedTorusClass` (= 𝕃 − 1), `nativeTorusClass B`,
  `ambientPuiseuxComparison_nativeTorusClass`.
- Galois: `CompatibleRoots ℂ`, `finiteRootProjection n` (onto μ_n, surjective), `rvAction η : RV ≃ RV`,
  `carrierAction_fixes_base`, `remark_5_13`, `kummerOriginalRVEquiv`.
  Finite levels on RV: `HasFrameSupport N a A`, `original_finite_frame_partition`,
  `rational_tuple_common_level`.
- Roots in Γ: `gammaDefinableClosure_nonzero_power_root d hd a δ hδ (ha : a ^ d = δ)`.
- Lemma 5.12: `monomial_decomposition_5_12`, `GroundMonomialPiece`.

## Built in Section 8 (formerly missing)

- The lattice `m⁻¹ℤ` (`InLattice`), rational values, definability of `qpow π q`, and the Galois
  action of compatible roots on the concrete model (`GaloisLattice`, `IsoLattice`, `MapLattice`).
- `R[T]†` and the limit (`RationalSeries`), Hrushovski–Loeser Lemma 8.5.2 (`lemma_8_9`,
  `lemma_8_9_rat`), `h_m`, Lemma 8.3, the zeta series and Theorem 8.11 on the RV side
  (`Theorem811`). The global (twist:C) formula was not needed: the evaluation side is computed on
  product generators `[g♯ × V]` (`Ediamond_sharp`, `Ediamond_res`).
- Useful library facts found on the way: `RVBoundedDecomposition.bounded_value` and `ringValue`
  (every doubly bounded class is a sum of products), `RESAllBoundedFiniteBalancing.finite_balance`
  with `gammaMap_class` (class of the lift of a finite Γ-set), `GammaBoundedMapImage.bounded_map_image`,
  `GammaTupleMaps.graph_definable`, `GammaBijectiveRelations.integrateAll_bijOn`,
  `GammaPointFamilies.integrateAll_singleton`, `nativeRVEvaluation_gamma/_res/_underlyingIso`.
- `MilnorFiber`: `milnorObject P f` (𝒳_f for `X = 𝔸^d`), `theorem_8_11_milnor`. Uses
  `mvPolynomialCode_definable/_eq` (polynomial maps), `rawOpenBall_definable`,
  `ambientComplexFieldHom_base_mem`, `PuiseuxOriginal.constant_valuation`, Section 6's
  `gammaOneMap`, `gamma_real_codes_iff`, `rv_eq_of_value_close`.
- `VolComparison`: Remark 8.14 (`remark_8_14`, `milnor_fiber_vol`). Uses Corollary 7.27's
  `left_object`, `forgetNormalized`, `bottomLeft`; `puiseuxBoundedVFVolume`;
  `GammaBoundedFamilies.integrateAll_bounded_comparison` (χ_b = χ_g on bounded families);
  `resGroundTransferReduced_objectClass`, `realGammaGround_definable_iff`,
  `ambientPuiseuxComparison_nativeTorusClass`. New: `integrateAll_base` (the Euler integral does not
  depend on the base of definability).

- Truncations and Lemma 8.6 (2026-11-21): `fullClass`, `fullClass_cutoff`, `fullClass_scale`,
  `fullClass_eq_of_ambient`, `chain_teq`, `lift_class`, `ambient_chart_class`, `milnor_zeta_coeff`,
  `z_coeff_change`. Section 6 interfaces used: `SpecialCovariantChain.properHomeomorphism`,
  `ProperCovariant.target_properInvariant`, `properInvariant_uniform_named_radius`,
  `properInvariant_uniform_named_upper_vf_bound`, `continuous_mixed_focus_uniform_named_covariance`
  (full covariance; the RV-pullback hypothesis of the erased version is avoided),
  `lemma_6_21_vfGenerated`, `isomorphic_of_liftData`; Section 7: `integralRing_ringClass`,
  `vfClass_iso`, `intQ_lift`, `lemma_6_33_diamond`, `chartOf`/`objOf`.

- (z:coeff:change) for smooth affine `X` (2026-11-21): `zeta_coeff_of_form_one` (any object with
  form `1`), `EtaleCoords`, `EtaleCoords.chart`, `IsJetX`, `jetObjectX`, `jetClassX`,
  `near_coeffSet`, `chart_rawClass`, `z_coeff_change_smooth`; general-dimension tools `rawClass`,
  `rawClass_eq_of_correspondence`, `rawClass_eq_of_thickened`, `exists_concrete_imageG`,
  `concrete_image_rationalG`, `invMapG`. Section 8 interfaces used from `MilnorSmooth`:
  `milnorObjectX`, `milnorIntegralX`, `milnorX_invariant`, `milnorX_maximal`, `mem_milnorSetX_iff`,
  `chartDefMap`.

- Remark 8.15 (2026-11-21, `Remark815`, `SameType`): `remark_8_15_class`, `remark_8_15_integral`,
  `remark_8_15`, `remark_8_15_affine`, `remark_8_15_smooth`, `remark_8_15_milnor`,
  `remark_8_15_milnor_smooth`; objects `XfObj` (`sourceSet`), `XtObj` (`fiberSet` at `t`), `RObj`
  (lift of `({1}, rv(t))`); `same_type`, `same_type_sum`, `rv_poly_eq`, `definable_extract_param`,
  `bijGraph_definable`, `gammaGround_empty_definable`. Library interfaces used:
  `native_arbitrary_vf_pullback_preparation` (any small base), `DefinableOver.quantifier_free`,
  `MixedPolynomialSupport.formula_iff_of_support`, `factor_X_nonzero_constant`,
  `rv_multiply_same_leading_term`, `gammaGroundFiniteRVFibres_iff`, `nativePositiveVFClass_bijection`,
  `gammaGroundVFSemiringClass_product`, `mem_gammaGroundMixedProductDomain`,
  `nativeVFChartIntegral_lift_class`, `RVOrdinaryRing.objectClass_iso`, `RVForgetScissors.ofMap`,
  `RVSharpCharts.identity_graph_definable`, `RESPointTuples.tuple_definable`,
  `gammaGroundDefinable_iff_rvBase`, `tuple_singleton_definable_base`, `GammaGroundMap.const`,
  `emptyGamma_sorted_definable_iff`, `RVRadiusGenerators.oneCode_definable`,
  `nativeRVEvaluation_point`; Section 8: `Truncation.chartCo`, `chartCo_bijective`, `sourceCodes`.

## Does not exist yet

- Nothing in Section 8.
