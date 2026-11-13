import «section 4».GammaWeightProfiles
import «section 4».GammaConstantPushforward
import «section 4».GammaMapOrder

/-! The actual Gamma-side input for the h calculation in Proposition 4.7:
the positive ray with weight -id has corrected weight zero, hence profiles
-p_0 geometrically and zero for the bounded Euler theory. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCounterweightedRay
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaMapOrder GammaWeightProfiles
open GammaIndicators GammaIntegerFamilies GammaIteratedIntegral GammaConstantPushforward EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def positiveRay : Set (Fin 1 → Values.Gamma (M := M)) := {z | 1 < z 0}

theorem positiveRay_definable (B : Base (M := M)) : GammaDefinable B (positiveRay (M := M)) :=
  lt_maps_definable B _ _ (constant_definable B 1 (GammaGroupNames.one_definable_base B))
    (projection_definable B 0)

def inverseCoordinate (z : Fin 1 → Values.Gamma (M := M)) : Values.Gamma (M := M) := (z 0)⁻¹

theorem inverseCoordinate_definable (B : Base (M := M)) : MapDefinable B (inverseCoordinate (M := M)) :=
  inverse_definable B _ (projection_definable B 0)

theorem correctedWeight_inverse (z : Fin 1 → Values.Gamma (M := M)) :
    correctedWeight inverseCoordinate z = 1 := by
  simp [correctedWeight, inverseCoordinate]

theorem positiveRay_integral (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) :
    integrateAll h00 hκ hs B hr hγ k 1 (indicatorFamily B positiveRay (positiveRay_definable B)) =
      k.rayValue := by
  have h := integrateAll_unary_from_euler h00 hκ hs B hr hγ k
    (indicatorFamily B positiveRay (positiveRay_definable B)) (ray k 0) (by
      intro γ
      rw [ray_eval]
      change (if ![γ] ∈ positiveRay then (1 : ℤ) else 0) = if 0 < toPaperGamma γ then 1 else 0
      have he : (0 : PaperGamma (M := M)) < toPaperGamma γ ↔ (1 : Values.Gamma (M := M)) < γ := Iff.rfl
      by_cases hγ : 1 < γ <;> simp [positiveRay, he, hγ])
  exact h.trans (totalEuler_ray k 0)

theorem counterweighted_ray_profile (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) :
    (profile h00 hκ hs B hr hγ k positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B)).val = k.rayValue • point k 0 := by
  have h := pushforward_constant h00 hκ hs B hr hγ k (correctedWeight inverseCoordinate)
    (by
      have hd := correctedWeight_definable B inverseCoordinate (inverseCoordinate_definable B)
      unfold MapDefinable at hd
      convert hd using 1
      ext z
      change z 0 = correctedWeight inverseCoordinate (Fin.tail z) ↔
        z 0 = correctedWeight inverseCoordinate (fun i => z i.succ)
      have he : Fin.tail z = (fun i => z i.succ) := by funext i; rfl
      rw [he]) 1 correctedWeight_inverse (indicatorFamily B positiveRay (positiveRay_definable B))
  rw [positiveRay_integral] at h
  exact h

theorem counterweighted_ray_geometric (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    (profile h00 hκ hs B hr hγ EulerKind.geometric positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B)).val = -point EulerKind.geometric 0 := by
  rw [counterweighted_ray_profile]
  exact neg_one_zsmul _

theorem counterweighted_ray_bounded (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    (profile h00 hκ hs B hr hγ EulerKind.bounded positiveRay (positiveRay_definable B)
      inverseCoordinate (inverseCoordinate_definable B)).val = 0 := by
  rw [counterweighted_ray_profile]
  exact zero_zsmul _

end DiamondIntegral.Section4.GammaCounterweightedRay
