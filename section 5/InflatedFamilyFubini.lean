import «section 5».InflatedGammaUniformRepresentatives
import «section 5».InflatedGammaBasePartition

/-! # Inflated-family Fubini (Theorem*, Section 5)

Final assembly of the paper's Theorem* "Inflated-family Fubini". Notation:
`R = RESDimensionFreeReduction.Ring G.base`, `g = nativeTorusClass G.base` (the
class `[G_m]`), `E_b ∫ = section5BoundedVFIntegral G hc` and, for a
`G.base`-definable `E ⊆ Γ^n`,
`χ_b(E) = GammaIteratedIntegral.integrateAll G.model00 … .bounded n (indicatorFamily G.base E _)`.

`inflated_family_fubini`: for a definable family `𝒜 ⊆ Γ^n × VF^m × RV^s` with
finite RV fibres there is a finite `G.base`-definable partition `(E_a)` of `Γ^n`
and classes `v_a ∈ R` such that
* `E_b ∫ [A_γ] = v_a` for every `γ ∈ E_a` with `G.base`-definable coordinates
  (equation `trop:fub:cons`);
* the parameters with empty fibres form a union of pieces, on which `v_a = 0`;
* `E_b ∫ [A^inf] = g^n · ∑_a χ_b(E_a) • v_a` (equation `fubini:inflated:RES`).

Proof (paper, "The total inflated space"): Track A
(`GammaVFFamily.uniform_representatives`) gives uniform RV representatives
`U l ⊆ Γ^n × RV^{r l}` computing the fibre values and the value of `A^inf`
through actual bijections. Track B is applied to each inflation
`(U l).gammaRVInflation`; it is re-run here (`inflatedFubini_relative_values`)
to also record that every value set `J_{l,i}` lies over the support of `U l`
(needed for the empty-fibre clause). Module 8
(`inflated_gamma_base_partition`) refines the supports of the `U l` and the
level sets of all slice Euler characteristics, and converts
`∑ χ_b(J_{l,i}) c_{l,i}` into `∑_a χ_b(E_a) v_a` with
`c_{l,i} = [W_{l,i}] g^{ℓ_{l,i}}` and `v_a = ∑ e_{(l,i),a} c_{l,i}`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open scoped Function
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
noncomputable section
namespace DiamondIntegral.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

/-! ### Value sets of relative charts lie over the parameter support -/

/-- If `(γ, η)` lies in the value set of a relative monomial chart of `X`, then
some point of `X` has first value coordinates `γ`. -/
theorem inflatedFubini_chart_support {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n + r))}
    (C : RelativeMonomialChart X) (γ : Fin n → Values.Gamma (M := M))
    (η : Fin C.freeArity → Values.Gamma (M := M)) (h : Fin.append γ η ∈ C.gamma.carrier) :
    ∃ (z : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → (CanonicalRV.RVSort M)ˣ),
      rvUnitTupleValues z = γ ∧ Fin.append z u ∈ X.carrier := by
  obtain ⟨z, hz⟩ := rvUnitTupleValues_surjective n γ
  obtain ⟨y, hy⟩ := rvUnitTupleValues_surjective C.freeArity η
  obtain ⟨w, hw⟩ := C.residue_nonempty
  have hNu : integerMonomialMap C.matrix (integerMonomialMap C.inverse (Fin.append w y)) =
      Fin.append w y := by
    rw [integerMonomialMap_comp, C.matrix_mul_inverse, integerMonomialMap_one]
  have htop : inflatedTop C.matrix (integerMonomialMap C.inverse (Fin.append w y)) = w := by
    funext i
    rw [inflatedTop_apply, hNu, Fin.append_left]
  have hbot : inflatedBottom C.matrix (integerMonomialMap C.inverse (Fin.append w y)) = y := by
    funext i
    rw [inflatedBottom_apply, hNu, Fin.append_right]
  refine ⟨z, integerMonomialMap C.inverse (Fin.append w y), hz, C.source_subset ((C.mem_iff _ _).mpr ⟨?_, ?_⟩)⟩
  · rw [htop]
    exact hw
  · rw [hz, hbot, hy]
    exact h

/-- A point of a zero stratum comes from a point of `X` with the same first
coordinates. -/
theorem inflatedFubini_stratum_support (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)))
    (I : Finset (Fin r)) (z : Fin n → (CanonicalRV.RVSort M)ˣ) (w : Fin I.card → (CanonicalRV.RVSort M)ˣ)
    (h : Fin.append z w ∈ (inflatedStratum X I).carrier) :
    ∃ u : Fin r → CanonicalRV.RVSort M, Fin.append (inflatedUnitsToRV z) u ∈ X.carrier := by
  obtain ⟨x, hx, hxw⟩ := h
  obtain ⟨hsplit, _⟩ := inflatedStratum_restrict hxw
  obtain ⟨hxX, _⟩ := (inflatedPattern_iff X _ I x).mp hx
  refine ⟨fun k => x (Fin.natAdd n k), ?_⟩
  rw [← hsplit]
  exact hxX

/-- Track B's `inflated_relative_monomial_values`, re-run on the same
decomposition, with the additional statement that every value set `J_i` lies
over the support of `X` in the first `n` value coordinates. -/
theorem inflatedFubini_relative_values {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) (n + r)))
    (hnz : ∀ x ∈ X.carrier, ∀ i : Fin n, x (Fin.castAdd r i) ≠ 0)
    (hX : ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → CanonicalRV.RVSort M),
      rvUnitTupleValues z = rvUnitTupleValues z' →
      Fin.append (inflatedUnitsToRV z) u ∈ X.carrier → Fin.append (inflatedUnitsToRV z') u ∈ X.carrier) :
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → RelativeValueTerm hc B n),
      (∀ i (γ : Fin n → Values.Gamma (M := M)) (η : Fin (T i).freeArity → Values.Gamma (M := M)),
        Fin.append γ η ∈ (T i).gamma.carrier →
        ∃ (z : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → CanonicalRV.RVSort M),
          rvUnitTupleValues z = γ ∧ Fin.append (inflatedUnitsToRV z) u ∈ X.carrier) ∧
      ∀ (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) (kind : EulerKind),
        nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
          ∑ i, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (T i).residue *
            nativeTorusClass B ^ (n + (T i).freeArity) *
              relativeGammaEuler h00 hκ hs hr hγ kind (T i).gamma ∧
        ∀ (γ : Fin n → Values.Gamma (M := M)) (F : GammaGroundDefSet hc B (rawRVSpace (M := M) r)),
          (∀ u, u ∈ F.carrier ↔ ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
            Fin.append (inflatedUnitsToRV z) u ∈ X.carrier) →
          ∀ (K : ∀ i, GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (T i).freeArity))),
            (∀ i η, η ∈ (K i).carrier ↔ Fin.append γ η ∈ (T i).gamma.carrier) →
            nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind F =
              ∑ i, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (T i).residue *
                nativeTorusClass B ^ (T i).freeArity *
                  relativeGammaEuler h00 hκ hs hr hγ kind (K i) := by
  choose N C hd hcov using fun I : Finset (Fin r) =>
    relative_monomial_decomposition hκ hs h00 hr hγ hΓ (inflatedStratum X I)
      (fun z z' w hzz hw => inflatedStratum_invariant X hX I z z' w hzz hw)
  refine ⟨(I : Finset (Fin r)) × Fin (N I), inferInstance, fun i => (C i.1 i.2).toTerm, ?_, ?_⟩
  · rintro ⟨I, j⟩ γ η h
    obtain ⟨z, w, hz, hw⟩ := inflatedFubini_chart_support (C I j) γ η h
    obtain ⟨u, hu⟩ := inflatedFubini_stratum_support X I z w hw
    exact ⟨z, u, hz, hu⟩
  intro linear kind
  constructor
  · rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind X
      (fun I => nativeRVZeroPatternBase X (Fin.natAdd n) I)
      (fun I J hne => nativeRVZeroPatternBase_disjoint X _ I J hne)
      (nativeRVZeroPatternBase_cover X _), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro I _
    obtain ⟨h1, h2⟩ := inflatedStratum_conditions X hnz I
    rw [← inflatedUnitStratum_value h00 linear hκ hs hr hγ hΓ kind _ _ h1 h2]
    exact relative_charts_native_value h00 linear hκ hs hr hγ hΓ kind (C I) (hd I) (hcov I)
  · intro γ F hF K hK
    rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind F
      (fun I => nativeRVZeroPatternBase F id I)
      (fun I J hne => nativeRVZeroPatternBase_disjoint F _ I J hne)
      (nativeRVZeroPatternBase_cover F _), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro I _
    obtain ⟨h1, h2⟩ := inflatedFibreStratum_conditions F I
    rw [← inflatedUnitStratum_value h00 linear hκ hs hr hγ hΓ kind _ _ h1 h2]
    exact relative_charts_fibre_value h00 linear hκ hs hr hγ hΓ kind (C I) (hd I) (hcov I) γ
      (inflatedFibreStratum F I) (inflatedFibreStratum_mem X γ F hF I)
      (fun c => K ⟨I, c⟩) (fun c => hK ⟨I, c⟩)

/-! ### The inflations of the uniform representatives -/

theorem inflatedFubini_ne_zero_of_vrv {t : CanonicalRV.RVSort M} {γ : Values.Gamma (M := M)}
    (h : Values.vrv t = γ.val) : t ≠ 0 := by
  intro h0
  apply γ.property
  rw [← h, Values.vrv_eq_infinity_iff, h0]
  exact RVOperations.zero_val

theorem inflatedFubini_unitValues_iff {k : ℕ} (z : Fin k → (CanonicalRV.RVSort M)ˣ)
    (γ : Fin k → Values.Gamma (M := M)) :
    rvUnitTupleValues z = γ ↔ ∀ i, Values.vrv (inflatedUnitsToRV z i) = (γ i).val := by
  constructor
  · intro h i
    exact congrArg Subtype.val (congrFun h i)
  · intro h
    funext i
    exact Subtype.ext (h i)

variable (U : GammaGroundDefSet hc B ((inflatedGammaPower hc n).prod (rawRVSpace (M := M) r)))

/-- The value coordinates of the inflation are nonzero. -/
theorem inflatedFubini_inflation_ne_zero :
    ∀ x ∈ U.gammaRVInflation.carrier, ∀ i : Fin n, x (Fin.castAdd r i) ≠ 0 := by
  rintro x ⟨γ, hγ, _⟩ i
  exact inflatedFubini_ne_zero_of_vrv (hγ i)

/-- The inflation depends on its value coordinates only through their values. -/
theorem inflatedFubini_inflation_invariant :
    ∀ (z z' : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → CanonicalRV.RVSort M),
      rvUnitTupleValues z = rvUnitTupleValues z' →
      Fin.append (inflatedUnitsToRV z) u ∈ U.gammaRVInflation.carrier →
        Fin.append (inflatedUnitsToRV z') u ∈ U.gammaRVInflation.carrier := by
  intro z z' u hzz h
  obtain ⟨γ, hγ, hU⟩ := (U.append_mem_gammaRVInflation _ u).mp h
  refine (U.append_mem_gammaRVInflation _ u).mpr ⟨γ, fun i => ?_, hU⟩
  rw [← hγ i]
  exact (congrArg Subtype.val (congrFun hzz i)).symm

/-- The fibre of the inflation over a value tuple `γ` is the row of `U` at `γ`. -/
theorem inflatedFubini_inflation_fibre (γ : Fin n → Values.Gamma (M := M))
    (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) (u : Fin r → CanonicalRV.RVSort M) :
    u ∈ (U.gammaFibre γ hγ).carrier ↔ ∃ z : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitTupleValues z = γ ∧
      Fin.append (inflatedUnitsToRV z) u ∈ U.gammaRVInflation.carrier := by
  constructor
  · intro hu
    obtain ⟨z, hz⟩ := rvUnitTupleValues_surjective n γ
    exact ⟨z, hz, (U.append_mem_gammaRVInflation _ u).mpr
      ⟨γ, (inflatedFubini_unitValues_iff z γ).mp hz, hu⟩⟩
  · rintro ⟨z, hz, h⟩
    obtain ⟨γ', hγ', hU⟩ := (U.append_mem_gammaRVInflation _ u).mp h
    rw [inflated_gamma_unique hγ' ((inflatedFubini_unitValues_iff z γ).mp hz)] at hU
    exact hU

/-- A point of the inflation over `γ` puts `γ` in the support of `U`. -/
theorem inflatedFubini_inflation_support (γ : Fin n → Values.Gamma (M := M))
    (z : Fin n → (CanonicalRV.RVSort M)ˣ) (u : Fin r → CanonicalRV.RVSort M)
    (hz : rvUnitTupleValues z = γ) (h : Fin.append (inflatedUnitsToRV z) u ∈ U.gammaRVInflation.carrier) :
    ∃ w, (γ, w) ∈ U.carrier := by
  obtain ⟨γ', hγ', hU⟩ := (U.append_mem_gammaRVInflation _ u).mp h
  rw [inflated_gamma_unique hγ' ((inflatedFubini_unitValues_iff z γ).mp hz)] at hU
  exact ⟨u, hU⟩

/-! ### Assembly -/

/-- The coefficient `c = [W] g^ℓ` of a relative value term, in the bounded
reduced RES ring of the original Gamma ground. -/
def RelativeValueTerm.inflatedFubiniCoeff (G : GammaGroundContext M)
    (T : RelativeValueTerm hc G.base n) : RESDimensionFreeReduction.Ring G.base :=
  nativeUnitRVSetValue G.model00 GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated hc
      G.base G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded T.residue *
    nativeTorusClass G.base ^ T.freeArity

/-- **Theorem\* (Inflated-family Fubini)**, equations `trop:fub:cons` and
`fubini:inflated:RES`. For a definable family `𝒜 ⊆ Γ^n × VF^m × RV^s` with finite
RV fibres over the original Gamma ground, there is a finite `G.base`-definable
partition `(E a)` of `Γ^n` and classes `v a ∈ R` such that
* `E_b ∫ [A_γ] = v a` for every `γ ∈ E a` with `G.base`-definable coordinates;
* the parameters with empty fibres form a union of pieces, where `v a = 0`;
* `E_b ∫ [A^inf] = g^n ∑ₐ χ_b(E a) • v a`, with `g = [G_m] = nativeTorusClass G.base`. -/
theorem inflated_family_fubini (G : GammaGroundContext M) (A : GammaVFFamily hc G.base n) :
    ∃ (α : Type) (_ : Fintype α) (E : α → Set (Fin n → Values.Gamma (M := M)))
      (hE : ∀ a, GammaOrderLogic.GammaDefinable G.base (E a))
      (v : α → RESDimensionFreeReduction.Ring G.base),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧
      (∀ a, (∃ γ ∈ E a, A.row γ = ∅) → (∀ γ ∈ E a, A.row γ = ∅) ∧ v a = 0) ∧
      (∀ a γ (hγ : ∀ i, GammaDefinableClosureAtBase G.base (γ i)), γ ∈ E a →
        section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ)) = v a) ∧
      section5BoundedVFIntegral G hc (nativeVFClass A.inflated) =
        nativeTorusClass G.base ^ n *
          ∑ a, (GammaIteratedIntegral.integrateAll G.model00 G.uncountable.le G.saturated G.base
            G.small_real G.small_gamma .bounded n (GammaIndicators.indicatorFamily G.base (E a) (hE a))) •
              v a := by
  obtain ⟨K, r, U, P, -, -, -, -, -, hrow, -, hfibsum, htot⟩ := A.uniform_representatives G
  choose ι hι T hsupp hval using fun l =>
    inflatedFubini_relative_values G.uncountable.le G.saturated G.model00 G.small_real G.small_gamma
      G.nontrivial_definable_gamma (U l).gammaRVInflation (inflatedFubini_inflation_ne_zero (U l))
      (inflatedFubini_inflation_invariant (U l))
  let _ : ∀ l, Fintype (ι l) := hι
  have hD : ∀ l, GammaOrderLogic.GammaDefinable G.base {γ | ∃ w, (γ, w) ∈ (U l).carrier} := fun l =>
    (Section4.Section3GammaCodeBridge.native_iff (hc := hc) _).mp (U l).definable.exists_snd
  obtain ⟨α, hα, E, hE, e, hEdisj, hEcov, hEref, -, -, hEslice, hEzero, hEsum⟩ :=
    inflated_gamma_base_partition G.model00 G.uncountable.le G.saturated G.small_real G.small_gamma
      G.nontrivial_definable_gamma .bounded (fun p : (Σ l, ι l) => (T p.1 p.2).freeArity)
      (fun p => (T p.1 p.2).gamma) (fun l => {γ | ∃ w, (γ, w) ∈ (U l).carrier}) hD
  refine ⟨α, hα, E, hE, fun a => ∑ p : (Σ l, ι l), e p a • (T p.1 p.2).inflatedFubiniCoeff G,
    hEdisj, hEcov, ?_, ?_, ?_⟩
  · -- the empty-fibre region is a union of pieces, with value zero
    rintro a ⟨γ₀, hγ₀a, hγ₀row⟩
    have hnot : ∀ l, γ₀ ∉ {γ | ∃ w, (γ, w) ∈ (U l).carrier} := by
      rintro l ⟨w, hw⟩
      have hw' : w ∈ ((U l).gammaFibreOver γ₀).carrier := hw
      rw [(hrow γ₀).mp hγ₀row l] at hw'
      exact hw'
    have hdisjD : ∀ l, Disjoint (E a) {γ | ∃ w, (γ, w) ∈ (U l).carrier} := by
      intro l
      rcases hEref l a with hsub | hd
      · exact absurd (hsub hγ₀a) (hnot l)
      · exact hd
    refine ⟨fun γ hγa => (hrow γ).mpr (fun l => ?_), ?_⟩
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact Set.disjoint_left.mp (hdisjD l) hγa ⟨w, hw⟩
    · apply Finset.sum_eq_zero
      rintro ⟨l, i⟩ _
      have h0 : e ⟨l, i⟩ a = 0 := hEzero ⟨l, i⟩ a γ₀ hγ₀a (fun η hη => by
        obtain ⟨z, u, hz, hzu⟩ := hsupp l i γ₀ η hη
        exact hnot l (inflatedFubini_inflation_support (U l) γ₀ z u hz hzu))
      rw [h0, zero_smul]
  · -- constancy of fibre values on each piece
    intro a γ hγ hγa
    have hγ' := inflatedGamma_singleton_definable (hc := hc) hγ
    rw [hfibsum γ hγ]
    have hterm : ∀ l, section5BoundedRVSetValue G hc ((U l).gammaFibre γ hγ) =
        ∑ i, e ⟨l, i⟩ a • (T l i).inflatedFubiniCoeff G := by
      intro l
      have h := (hval l GammaQE.gamma_piecewise_rational_affine .bounded).2 γ ((U l).gammaFibre γ hγ)
        (inflatedFubini_inflation_fibre (U l) γ hγ)
        (fun i => relativeGammaSlice (T l i).gamma γ hγ') (fun i η => Iff.rfl)
      refine h.trans (Finset.sum_congr rfl (fun i _ => ?_))
      have h5 : relativeGammaEuler G.model00 G.uncountable.le G.saturated G.small_real G.small_gamma .bounded
          (relativeGammaSlice (T l i).gamma γ hγ') =
          ((e ⟨l, i⟩ a : ℤ) : RESDimensionFreeReduction.Ring G.base) :=
        hEslice ⟨l, i⟩ a γ hγ' hγa
      rw [h5, zsmul_eq_mul, RelativeValueTerm.inflatedFubiniCoeff]
      ring
    rw [Finset.sum_congr rfl (fun l _ => hterm l)]
    exact (Fintype.sum_sigma (fun p : (Σ l, ι l) => e p a • (T p.1 p.2).inflatedFubiniCoeff G)).symm
  · -- the inflated total space
    rw [htot]
    have hterm : ∀ l, section5BoundedRVSetValue G hc (U l).gammaRVInflation =
        nativeTorusClass G.base ^ n *
          ∑ i, (GammaIteratedIntegral.integrateAll G.model00 G.uncountable.le G.saturated G.base
            G.small_real G.small_gamma .bounded (n + (T l i).freeArity)
              (GammaIndicators.indicatorFamily G.base (T l i).gamma.carrier
                (Section3GammaChartBridge.chart (T l i).gamma).support_definable)) •
            (T l i).inflatedFubiniCoeff G := by
      intro l
      refine ((hval l GammaQE.gamma_piecewise_rational_affine .bounded).1).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [zsmul_eq_mul, RelativeValueTerm.inflatedFubiniCoeff, pow_add]
      ring
    rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum]
    congr 1
    exact (Fintype.sum_sigma (fun p : (Σ l, ι l) =>
      (GammaIteratedIntegral.integrateAll G.model00 G.uncountable.le G.saturated G.base
        G.small_real G.small_gamma .bounded (n + (T p.1 p.2).freeArity)
          (GammaIndicators.indicatorFamily G.base (T p.1 p.2).gamma.carrier
            (Section3GammaChartBridge.chart (T p.1 p.2).gamma).support_definable)) •
        (T p.1 p.2).inflatedFubiniCoeff G)).symm.trans
      ((hEsum GammaQE.gamma_piecewise_rational_affine).2 _ _)

end DiamondIntegral.Section5
