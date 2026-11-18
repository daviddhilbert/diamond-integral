import «section 5».InflatedRelativeMonomialValues
import «section 5».GammaIntegralBaseIndependence
import «section 4».GammaPrefixIntegration
import «section 4».GammaFinitePartitions

/-! # A separate base partition (inflated-family Fubini, module 8)

The base-partition step of the proof of the inflated-family Fubini theorem
(paper, "A separate base partition"). The paper refines the closed polyhedra
of the projections; here Section 4's Gamma-Fubini machinery does the work:
the prefix integral (`GammaPrefixIntegration.integratePrefix`) of the
block-order indicator of each `J_i` is an original-base integer family on
`Γ^n` (finite range, definable level sets), and its value at `γ` is the
actual integral of the slice `J_{i,γ}` over `withGamma B (range γ)`
(`integratePrefix_fibre`). The common refinement of all these level-set
partitions and of the extra sets `D_k` is the base partition.

Notation: `χ_B(S) := GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind k
(indicatorFamily B S _)` (an integer), so that
`relativeGammaEuler h00 hκ hs hr hγ kind J = (χ_B(J.carrier) : Ring B)` by `rfl`.

Exported:
```
theorem gamma_common_level_partition (B) (n) (q : τ → familySubgroup B n) :
    ∃ α _ E (_ : ∀ a, GammaDefinable B (E a)) (v : τ → α → ℤ),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧ ∀ j a γ, γ ∈ E a → (q j).val γ = v j a
def inflatedSliceFamily (J : GammaGroundDefSet hc B (Γ^(n+ℓ))) (γ) :
    familySubgroup (withGamma B (range γ)) ℓ          -- indicator of {η | Fin.append γ η ∈ J}
theorem inflated_gamma_base_partition (h00 hκ hs hr hγ hΓ kind) (ℓ : ι → ℕ)
    (J : ∀ i, GammaGroundDefSet hc B (Γ^(n + ℓ i))) (D : τ → Set (Γ^n)) (hD) :
    ∃ α _ E hE (e : ι → α → ℤ),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧
      (∀ k a, E a ⊆ D k ∨ Disjoint (E a) (D k)) ∧
      (∀ i a γ, γ ∈ E a → ∫_{withGamma B (range γ)} inflatedSliceFamily (J i) γ = e i a) ∧
      (∀ i a γ, γ ∈ E a → ∀ K, (∀ η, η ∈ K ↔ Fin.append γ η ∈ J i) →
          χ_B(K) = e i a ∧ relativeGammaEuler K = e i a) ∧
      (∀ i a γ hγ', γ ∈ E a → relativeGammaEuler (relativeGammaSlice (J i) γ hγ') = e i a) ∧
      (∀ i a γ, γ ∈ E a → (∀ η, Fin.append γ η ∉ J i) → e i a = 0) ∧
      (GammaPiecewiseRationalAffineInput → (∀ i, χ_B(J i) = ∑ a, e i a * χ_B(E a)) ∧
        ∀ (R : Type u) [AddCommGroup R] (c : ι → R),
          ∑ i, χ_B(J i) • c i = ∑ a, χ_B(E a) • ∑ i, e i a • c i)
```
The partition and the coefficients depend only on `kind` (not on `linear`);
`linear` and `hΓ` enter only through the coordinate-permutation invariance
(`GammaFubiniPermutation.integrateAll_equiv`) relating the `(γ, η)` order of
`J_i` to Section 4's block order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open scoped Function
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open DiamondIntegral.Section4.GammaIntegerFamilies DiamondIntegral.Section4.GammaIndicators
open DiamondIntegral.Section4.GammaIteratedIntegral DiamondIntegral.Section4.GammaPrefixIntegration
noncomputable section
namespace DiamondIntegral.Section5

universe u

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

section LevelPartition

/-- The common refinement of the level-set partitions of finitely many
original-base integer families on `Γ^n`: a finite definable partition on
whose pieces every family is constant. -/
theorem gamma_common_level_partition (B : Base (M := M)) (n : ℕ) {τ : Type} [Fintype τ]
    (q : τ → familySubgroup B n) :
    ∃ (α : Type) (_ : Fintype α) (E : α → Set (Fin n → Values.Gamma (M := M)))
      (_ : ∀ a, GammaOrderLogic.GammaDefinable B (E a)) (v : τ → α → ℤ),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧
        ∀ j a γ, γ ∈ E a → (q j).val γ = v j a := by
  have hq : ∀ j, GammaFamilyIntegration.IntegerFamilyDefinable B (q j).val := fun j => (q j).property
  let S : τ → Finset ℤ := fun j => (hq j).1.toFinset
  refine ⟨(j : τ) → {x : ℤ // x ∈ S j}, inferInstance,
    fun a => ⋂ j, {γ | (q j).val γ = (a j : ℤ)},
    fun a => GammaQuantifierLogic.finite_iInter_definable_base B _ (fun j => (hq j).2 _),
    fun j a => (a j : ℤ), ?_, ?_, ?_⟩
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro γ ha hb
    apply hab
    funext j
    apply Subtype.ext
    exact (Set.mem_iInter.mp ha j).symm.trans (Set.mem_iInter.mp hb j)
  · intro γ
    exact ⟨fun j => ⟨(q j).val γ, (hq j).1.mem_toFinset.mpr ⟨γ, rfl⟩⟩,
      Set.mem_iInter.mpr fun j => rfl⟩
  · intro j a γ hγ
    exact Set.mem_iInter.mp hγ j

end LevelPartition

section Slices

/-- The slice `{η | (γ, η) ∈ J}` is definable over `B` with the coordinates
of `γ` adjoined. -/
theorem inflatedSlice_definable {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M)) :
    GammaOrderLogic.GammaDefinable (GammaBaseExtension.withGamma B (Set.range γ))
      {η : Fin ℓ → Values.Gamma (M := M) | Fin.append γ η ∈ J.carrier} := by
  have h := GammaBlockSlices.slice_definable_base B n ℓ (relativeGammaJoin J).carrier
    (Section3GammaChartBridge.chart (relativeGammaJoin J)).support_definable γ
  have he : {u : Fin ℓ → Values.Gamma (M := M) |
      FiniteTupleBlocks.join n ℓ u γ ∈ (relativeGammaJoin J).carrier} =
      {η | Fin.append γ η ∈ J.carrier} := Set.ext fun η => relativeGammaJoin_mem J η γ
  rw [← he]
  exact h

/-- The indicator of the slice `{η | (γ, η) ∈ J}` as an integer family over
`withGamma B (range γ)`; its integral is the fibre Euler characteristic at an
arbitrary (not necessarily definable) `γ`. -/
def inflatedSliceFamily {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M)) :
    familySubgroup (GammaBaseExtension.withGamma B (Set.range γ)) ℓ :=
  indicatorFamily _ {η | Fin.append γ η ∈ J.carrier} (inflatedSlice_definable J γ)

theorem inflatedSliceFamily_apply {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M)) (η : Fin ℓ → Values.Gamma (M := M)) :
    (inflatedSliceFamily J γ).val η = if Fin.append γ η ∈ J.carrier then 1 else 0 := rfl

/-- The block-order (integrated coordinates first) indicator of `J`. -/
def inflatedJoinFamily {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ)))) :
    familySubgroup B (n + ℓ) :=
  indicatorFamily B (relativeGammaJoin J).carrier
    (Section3GammaChartBridge.chart (relativeGammaJoin J)).support_definable

end Slices

section BasePartition
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (kind : EulerKind)

/-- The prefix integral of the block-order indicator of `J` at `γ` is the
slice integral over `withGamma B (range γ)`. -/
theorem inflatedSlice_integral_eq_prefix {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M)) :
    integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range γ)) hr
        (GammaParameterExtension.finite_gamma_extension_small hκ B hγ γ) kind ℓ
        (inflatedSliceFamily J γ) =
      (integratePrefix h00 hκ hs B hr hγ kind n ℓ (inflatedJoinFamily J)).val γ := by
  rw [integratePrefix_fibre]
  apply gamma_integral_parameter_independent
  intro u
  change (if Fin.append γ u ∈ J.carrier then (1 : ℤ) else 0) =
    if FiniteTupleBlocks.join n ℓ u γ ∈ (relativeGammaJoin J).carrier then 1 else 0
  rw [relativeGammaJoin_mem]

/-- A `B`-definable presentation `K` of the slice of `J` at `γ` has the same
Euler integral over `B` as the slice integral over `withGamma B (range γ)`. -/
theorem inflatedSlice_integral_eq_base {ℓ : ℕ}
    (J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ))))
    (γ : Fin n → Values.Gamma (M := M))
    (K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin ℓ)))
    (hK : ∀ η, η ∈ K.carrier ↔ Fin.append γ η ∈ J.carrier) :
    integrateAll h00 hκ hs B hr hγ kind ℓ
        (indicatorFamily B K.carrier (Section3GammaChartBridge.chart K).support_definable) =
      integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range γ)) hr
        (GammaParameterExtension.finite_gamma_extension_small hκ B hγ γ) kind ℓ
        (inflatedSliceFamily J γ) := by
  apply gamma_integral_parameter_independent
  intro u
  change (if u ∈ K.carrier then (1 : ℤ) else 0) = if Fin.append γ u ∈ J.carrier then 1 else 0
  exact if_congr (hK u) rfl rfl

end BasePartition

/-- **Base partition.** For finitely many original-ground value sets
`J_i ⊆ Γ^(n+ℓ_i)` (in `(γ, η)` order) and finitely many `B`-definable
`D_k ⊆ Γ^n`, a finite `B`-definable partition `(E_a)` of `Γ^n` refining
every `D_k`, and integers `e i a`, such that the slice Euler characteristic
of `J_i` at every `γ ∈ E_a` is `e i a` (over `withGamma B (range γ)` for
every `γ`, and over `B` whenever the slice is `B`-definable, e.g. for `γ`
with `B`-definable coordinates), and
`∑ᵢ χ(Jᵢ) • cᵢ = ∑ₐ χ(Eₐ) • ∑ᵢ e i a • cᵢ`. -/
theorem inflated_gamma_base_partition (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {ι : Type} [Fintype ι] (ℓ : ι → ℕ)
    (J : ∀ i, GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n + ℓ i))))
    {τ : Type} [Fintype τ] (D : τ → Set (Fin n → Values.Gamma (M := M)))
    (hD : ∀ k, GammaOrderLogic.GammaDefinable B (D k)) :
    ∃ (α : Type) (_ : Fintype α) (E : α → Set (Fin n → Values.Gamma (M := M)))
      (hE : ∀ a, GammaOrderLogic.GammaDefinable B (E a)) (e : ι → α → ℤ),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧
      (∀ k a, E a ⊆ D k ∨ Disjoint (E a) (D k)) ∧
      (∀ i a γ, γ ∈ E a →
        integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range γ)) hr
          (GammaParameterExtension.finite_gamma_extension_small hκ B hγ γ) kind (ℓ i)
          (inflatedSliceFamily (J i) γ) = e i a) ∧
      (∀ i a γ, γ ∈ E a →
        ∀ K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (ℓ i))),
          (∀ η, η ∈ K.carrier ↔ Fin.append γ η ∈ (J i).carrier) →
          integrateAll h00 hκ hs B hr hγ kind (ℓ i)
              (indicatorFamily B K.carrier (Section3GammaChartBridge.chart K).support_definable) =
            e i a ∧
          relativeGammaEuler h00 hκ hs hr hγ kind K = (e i a : RESDimensionFreeReduction.Ring B)) ∧
      (∀ i a γ (hγ' : GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) {γ}),
        γ ∈ E a →
        relativeGammaEuler h00 hκ hs hr hγ kind (relativeGammaSlice (J i) γ hγ') =
          (e i a : RESDimensionFreeReduction.Ring B)) ∧
      (∀ i a γ, γ ∈ E a → (∀ η, Fin.append γ η ∉ (J i).carrier) → e i a = 0) ∧
      (Section2.GammaPiecewiseRationalAffineInput (M := M) →
        (∀ i, integrateAll h00 hκ hs B hr hγ kind (n + ℓ i)
            (indicatorFamily B (J i).carrier (Section3GammaChartBridge.chart (J i)).support_definable) =
          ∑ a, e i a * integrateAll h00 hκ hs B hr hγ kind n (indicatorFamily B (E a) (hE a))) ∧
        ∀ (R : Type u) [AddCommGroup R] (c : ι → R),
          (∑ i, (integrateAll h00 hκ hs B hr hγ kind (n + ℓ i)
              (indicatorFamily B (J i).carrier
                (Section3GammaChartBridge.chart (J i)).support_definable)) • c i) =
            ∑ a, (integrateAll h00 hκ hs B hr hγ kind n (indicatorFamily B (E a) (hE a))) •
              (∑ i, e i a • c i)) := by
  obtain ⟨α, _, E, hE, v, hdisj, hcov, hval⟩ := gamma_common_level_partition B n
    (Sum.elim (fun i => integratePrefix h00 hκ hs B hr hγ kind n (ℓ i) (inflatedJoinFamily (J i)))
      (fun k => indicatorFamily B (D k) (hD k)))
  have hpv : ∀ i a γ, γ ∈ E a →
      (integratePrefix h00 hκ hs B hr hγ kind n (ℓ i) (inflatedJoinFamily (J i))).val γ =
        v (Sum.inl i) a := fun i a γ h => hval (Sum.inl i) a γ h
  have hslice : ∀ i a γ, γ ∈ E a →
      integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range γ)) hr
        (GammaParameterExtension.finite_gamma_extension_small hκ B hγ γ) kind (ℓ i)
        (inflatedSliceFamily (J i) γ) = v (Sum.inl i) a := fun i a γ h =>
    (inflatedSlice_integral_eq_prefix h00 hκ hs hr hγ kind (J i) γ).trans (hpv i a γ h)
  have hbase : ∀ i a γ, γ ∈ E a →
      ∀ K : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (ℓ i))),
        (∀ η, η ∈ K.carrier ↔ Fin.append γ η ∈ (J i).carrier) →
        integrateAll h00 hκ hs B hr hγ kind (ℓ i)
            (indicatorFamily B K.carrier (Section3GammaChartBridge.chart K).support_definable) =
          v (Sum.inl i) a := fun i a γ h K hK =>
    (inflatedSlice_integral_eq_base h00 hκ hs hr hγ kind (J i) γ K hK).trans (hslice i a γ h)
  refine ⟨α, inferInstance, E, hE, fun i a => v (Sum.inl i) a, hdisj, hcov, ?_, hslice,
    ?_, ?_, ?_, ?_⟩
  · -- refinement of every `D k`
    intro k a
    by_cases h : ∃ γ ∈ E a, γ ∈ D k
    · left
      obtain ⟨γ, hγa, hγD⟩ := h
      intro γ' hγ'
      have h1 : (if γ ∈ D k then (1 : ℤ) else 0) = v (Sum.inr k) a := hval (Sum.inr k) a γ hγa
      have h2 : (if γ' ∈ D k then (1 : ℤ) else 0) = v (Sum.inr k) a := hval (Sum.inr k) a γ' hγ'
      rw [ite_eq_left hγD] at h1
      by_contra hn
      rw [ite_eq_right hn] at h2
      omega
    · right
      exact Set.disjoint_left.mpr fun γ hγa hγD => h ⟨γ, hγa, hγD⟩
  · -- slices presented over `B`
    intro i a γ h K hK
    have hint := hbase i a γ h K hK
    exact ⟨hint, congrArg (fun z : ℤ => (z : RESDimensionFreeReduction.Ring B)) hint⟩
  · -- slices at `B`-definable value tuples
    intro i a γ hγ' h
    exact congrArg (fun z : ℤ => (z : RESDimensionFreeReduction.Ring B))
      (hbase i a γ h (relativeGammaSlice (J i) γ hγ') (fun η => Iff.rfl))
  · -- empty slices contribute zero
    intro i a γ h hempty
    have h0 : inflatedSliceFamily (J i) γ = 0 := by
      apply Subtype.ext
      funext η
      change (if Fin.append γ η ∈ (J i).carrier then (1 : ℤ) else 0) = 0
      rw [ite_eq_right (hempty η)]
    have hs' := hslice i a γ h
    rw [h0, map_zero] at hs'
    exact hs'.symm
  · -- the coefficient identity
    intro linear
    have hpref : ∀ i, integratePrefix h00 hκ hs B hr hγ kind n (ℓ i) (inflatedJoinFamily (J i)) =
        ∑ a, v (Sum.inl i) a • indicatorFamily B (E a) (hE a) := by
      intro i
      apply Subtype.ext
      funext γ
      change _ = GammaFinitePartitions.familyEvaluation B n γ
        (∑ a, v (Sum.inl i) a • indicatorFamily B (E a) (hE a))
      rw [map_sum]
      simp only [map_zsmul]
      change _ = ∑ a, v (Sum.inl i) a • (if γ ∈ E a then (1 : ℤ) else 0)
      obtain ⟨a₀, ha₀⟩ := hcov γ
      rw [Finset.sum_eq_single a₀
        (fun b _ hb => by
          rw [ite_eq_right (fun hγb => Set.disjoint_left.mp (hdisj hb) hγb ha₀), smul_zero])
        (fun h => absurd (Finset.mem_univ a₀) h), ite_eq_left ha₀, smul_eq_mul, mul_one]
      exact hpv i a₀ γ ha₀
    have htot : ∀ i, integrateAll h00 hκ hs B hr hγ kind (n + ℓ i)
        (indicatorFamily B (J i).carrier (Section3GammaChartBridge.chart (J i)).support_definable) =
        ∑ a, v (Sum.inl i) a *
          integrateAll h00 hκ hs B hr hγ kind n (indicatorFamily B (E a) (hE a)) := by
      intro i
      have hpull : GammaCoordinatePullback.pullback B (relativeJoinEquiv n (ℓ i))
          (indicatorFamily B (J i).carrier (Section3GammaChartBridge.chart (J i)).support_definable) =
          inflatedJoinFamily (J i) := Subtype.ext rfl
      have hperm := GammaFubiniPermutation.integrateAll_equiv h00 hκ hs B hr hγ kind linear hΓ
        (n + ℓ i) (n + ℓ i) (relativeJoinEquiv n (ℓ i))
        (indicatorFamily B (J i).carrier (Section3GammaChartBridge.chart (J i)).support_definable)
      rw [hpull] at hperm
      rw [← hperm, integrateAll_factor, AddMonoidHom.comp_apply, hpref i, map_sum]
      simp only [map_zsmul, smul_eq_mul]
    refine ⟨htot, ?_⟩
    intro R _ c
    simp_rw [htot, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

end DiamondIntegral.Section5
