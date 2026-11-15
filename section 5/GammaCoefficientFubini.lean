import «section 4».GammaPrefixIntegration
import «section 4».GammaFinitePartitions

/-! The finite coefficient assembly in relative Gamma push and the
inflated-family formula. Fibre values are actual integrals over the
displayed original base extended by the parameter values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
open GammaIntegerFamilies GammaIteratedIntegral GammaPrefixIntegration
open GammaFinitePartitions GammaIndicators GammaBlockSlices GammaParameterExtension
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem relativeGamma_finite_coefficients
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n m : ℕ) {ι α : Type} [Fintype ι] [Fintype α]
    (f : ι → familySubgroup B (n + m))
    (E : α → Set (Fin n → Values.Gamma (M := M)))
    (hE : ∀ a, GammaOrderLogic.GammaDefinable B (E a)) (e : ι → α → ℤ)
    (hf : ∀ i (y : Fin n → Values.Gamma (M := M)),
      integrateAll h00 hκ hs (GammaBaseExtension.withGamma B (Set.range y)) hr
        (finite_gamma_extension_small hκ B hγ y) k m
        ⟨slice (f i).val y, slice_definable B n m (f i).val (f i).property y⟩ =
          ∑ a, e i a * (if y ∈ E a then 1 else 0))
    {R : Type*} [AddCommGroup R] (c : ι → R) :
    (∑ i, (integrateAll h00 hκ hs B hr hγ k (n + m) (f i)) • c i) =
      ∑ a, (integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B (E a) (hE a))) •
        (∑ i, e i a • c i) := by
  have hp (i : ι) : integratePrefix h00 hκ hs B hr hγ k n m (f i) =
      ∑ a, e i a • indicatorFamily B (E a) (hE a) := by
    apply Subtype.ext
    funext y
    change (integratePrefix h00 hκ hs B hr hγ k n m (f i)).val y =
      familyEvaluation B n y (∑ a, e i a • indicatorFamily B (E a) (hE a))
    rw [map_sum]
    simp only [map_zsmul]
    change (integratePrefix h00 hκ hs B hr hγ k n m (f i)).val y =
      ∑ a, e i a • (if y ∈ E a then (1 : ℤ) else 0)
    rw [integratePrefix_fibre]
    simpa only [zsmul_eq_mul, Int.cast_id] using hf i y
  have ht (i : ι) : integrateAll h00 hκ hs B hr hγ k (n + m) (f i) =
      ∑ a, e i a * integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B (E a) (hE a)) := by
    rw [integrateAll_factor]
    change integrateAll h00 hκ hs B hr hγ k n
      (integratePrefix h00 hκ hs B hr hγ k n m (f i)) = _
    rw [hp i, map_sum]
    simp only [map_zsmul, zsmul_eq_mul, Int.cast_id]
  simp_rw [ht, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

end DiamondIntegral.Section5
