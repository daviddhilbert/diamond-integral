import «section 4».GammaCellSections

/-! Actual open ray and whole-line sections, completing the elementary
cylindrical shapes for geometric cell Euler integration. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCellUnboundedSections
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies
open GammaIndicators GammaIteratedIntegral GammaCellSections EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integrateFirst_specified (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (f : familySubgroup B (n + 1))
    (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
    (F : (Fin n → Values.Gamma (M := M)) → EulerFunction k (PaperGamma (M := M))) (w : ℤ)
    (heval : ∀ y a, f.val (Fin.cons a y) = if y ∈ C then F y (toPaperGamma a) else 0)
    (heuler : ∀ y ∈ C, totalEuler k (F y) = w) :
    integrateFirst h00 hκ hs B hr hγ k n f = w • indicatorFamily B C hC := by
  have hf : IntegerFamilyDefinable B f.val := f.property
  apply Subtype.ext
  funext y
  change integralFirst h00 B k f.val hf y = w • (indicatorFamily B C hC).val y
  by_cases hy : y ∈ C
  · have h := integralFirst_from_euler h00 B k f.val hf y (F y) (by
      intro a
      exact (heval y a).trans (ite_eq_left hy))
    rw [h, heuler y hy]
    simp [indicatorFamily, hy]
  · have h := integralFirst_from_euler h00 B k f.val hf y 0 (by
      intro a
      exact (heval y a).trans ((ite_eq_right hy).trans (eval_zero k (toPaperGamma a)).symm))
    rw [h, map_zero]
    simp [indicatorFamily, hy]

def upperRayCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ l (Fin.tail z) < z 0}

def lowerRayCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ z 0 < u (Fin.tail z)}

def lineCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C}

theorem integrateFirst_upperRay (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
    (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hR : GammaDefinable B (upperRayCell C l)) :
    integrateFirst h00 hκ hs B hr hγ k n (indicatorFamily B (upperRayCell C l) hR) =
      k.rayValue • indicatorFamily B C hC := by
  apply integrateFirst_specified h00 hκ hs B hr hγ k _ C hC
    (fun y => ray k (toPaperGamma (l y))) k.rayValue
  · intro y a
    have hle : toPaperGamma (l y) < toPaperGamma a ↔ l y < a := Iff.rfl
    by_cases hy : y ∈ C <;> simp [indicatorFamily, upperRayCell, hy, ray_eval, hle]
  · intro y _
    exact totalEuler_ray k _

theorem integrateFirst_lowerRay (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hR : GammaDefinable B (lowerRayCell C u)) :
    integrateFirst h00 hκ hs B hr hγ k n (indicatorFamily B (lowerRayCell C u) hR) =
      k.rayValue • indicatorFamily B C hC := by
  apply integrateFirst_specified h00 hκ hs B hr hγ k _ C hC
    (fun y => leftRay k (toPaperGamma (u y))) k.rayValue
  · intro y a
    have hle : toPaperGamma a < toPaperGamma (u y) ↔ a < u y := Iff.rfl
    by_cases hy : y ∈ C <;> simp [indicatorFamily, lowerRayCell, hy, leftRay_eval, hle]
  · intro y _
    exact totalEuler_leftRay k _

theorem integrateFirst_line (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
    (hR : GammaDefinable B (lineCell C)) :
    integrateFirst h00 hκ hs B hr hγ k n (indicatorFamily B (lineCell C) hR) =
      k.lineValue • indicatorFamily B C hC := by
  apply integrateFirst_specified h00 hκ hs B hr hγ k _ C hC (fun _ => line k) k.lineValue
  · intro y a
    by_cases hy : y ∈ C <;> simp [indicatorFamily, lineCell, hy, line_eval]
  · intro y _
    exact totalEuler_line k

end DiamondIntegral.Section4.GammaCellUnboundedSections
