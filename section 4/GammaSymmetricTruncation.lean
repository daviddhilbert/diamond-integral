import «section 4».GammaHigherProjection
import «section 4».GammaRadiusProfiles

/-! Actual restriction of a finite-dimensional family to a symmetric box.
The radius projection formula identifies its integral with unary truncation
of the actual radius profile. A radius is named only in the explicit base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaSymmetricTruncation
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaMapOrder GammaIntegerFamilies
open GammaIndicators GammaHigherPushforward GammaHigherProjection GammaRadius GammaRadiusProfiles
open GammaIteratedIntegral EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem interval_definable (B : Base (M := M)) (r : Values.Gamma (M := M))
    (hr : GammaDefinableClosureAtBase B r) :
    GammaDefinable B {z : Fin 1 → Values.Gamma (M := M) | r⁻¹ ≤ z 0 ∧ z 0 ≤ r} := by
  have hc := constant_definable (n := 1) B r hr
  have hp := projection_definable B (0 : Fin 1)
  have hl := lt_maps_definable B _ _ hp (inverse_definable B _ hc)
  have hu := lt_maps_definable B _ _ hc hp
  have h := GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.complement_definable_base B _ hl)
    (GammaRelationLogic.complement_definable_base B _ hu)
  convert h using 1
  ext z
  change (r⁻¹ ≤ z 0 ∧ z 0 ≤ r) ↔ ¬ z 0 < r⁻¹ ∧ ¬ r < z 0
  simp only [not_lt]

def intervalFamily (B : Base (M := M)) (r : Values.Gamma (M := M))
    (hr : GammaDefinableClosureAtBase B r) : familySubgroup B 1 :=
  indicatorFamily B _ (interval_definable B r hr)

theorem intervalFamily_eval (B : Base (M := M)) (r : Values.Gamma (M := M))
    (hr : GammaDefinableClosureAtBase B r) (a : Values.Gamma (M := M)) :
    (intervalFamily B r hr).val ![a] = if r⁻¹ ≤ a ∧ a ≤ r then 1 else 0 := by
  by_cases h : r⁻¹ ≤ a ∧ a ≤ r <;> simp [intervalFamily, indicatorFamily, h]

theorem intervalFamily_toEuler (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (r : Values.Gamma (M := M)) (hr : GammaDefinableClosureAtBase B r) :
    (GammaUnaryFamilyBridge.toEuler h00 B k (intervalFamily B r hr)).val =
      closedInterval k (-toPaperGamma r) (toPaperGamma r) := by
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change (GammaUnaryFamilyBridge.toEuler h00 B k (intervalFamily B r hr)).val (toPaperGamma γ) =
    closedInterval k (-toPaperGamma r) (toPaperGamma r) (toPaperGamma γ)
  rw [GammaUnaryFamilyBridge.toEuler_eval, intervalFamily_eval, closedInterval_eval]
  change (if r⁻¹ ≤ γ ∧ γ ≤ r then (1 : ℤ) else 0) = if r⁻¹ ≤ γ ∧ γ ≤ r then 1 else 0
  rfl

def truncateFamily (B : Base (M := M)) {n : ℕ} (f : familySubgroup B n)
    (r : Values.Gamma (M := M)) (hr : GammaDefinableClosureAtBase B r) : familySubgroup B n :=
  multiplyFamily B f (unaryCompose B (radius n) (radius_graph_definable B n) (intervalFamily B r hr))

theorem truncateFamily_eval (B : Base (M := M)) {n : ℕ} (f : familySubgroup B n)
    (r : Values.Gamma (M := M)) (hr : GammaDefinableClosureAtBase B r) (hpos : 1 ≤ r)
    (z : Fin n → Values.Gamma (M := M)) :
    (truncateFamily B f r hr).val z = if ∀ i, r⁻¹ ≤ z i ∧ z i ≤ r then f.val z else 0 := by
  change f.val z * (intervalFamily B r hr).val ![radius n z] = _
  rw [intervalFamily_eval]
  have hlower : r⁻¹ ≤ 1 := by simpa only [inv_one] using inv_le_inv_iff.mpr hpos
  have hlo : r⁻¹ ≤ radius n z := hlower.trans (one_le_radius n z)
  simp only [hlo, true_and, radius_le_iff n z r hpos]
  split_ifs <;> simp

theorem integral_truncateFamily (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (f : familySubgroup B n)
    (r : Values.Gamma (M := M)) (hradius : GammaDefinableClosureAtBase B r) :
    integrateAll h00 hκ hs B hr hγ k n (truncateFamily B f r hradius) =
      totalEuler k (truncate k (-toPaperGamma r) (toPaperGamma r)
        (radiusProfile h00 hκ hs B hr hγ k n f).val) := by
  have h := integral_projection h00 linear hκ hs B hr hγ hΓ k (radius n) (radius_graph_definable B n)
    f (intervalFamily B r hradius)
  rw [intervalFamily_toEuler] at h
  exact h

end DiamondIntegral.Section4.GammaSymmetricTruncation
