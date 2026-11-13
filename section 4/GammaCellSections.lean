import «section 4».GammaBijectiveRelations
import «section 4».EulerIntervals

/-! Actual graph and open-band sections of the Gamma integral. Their
Euler values are computed from point and interval functions, not assumed
as a cell-integration input. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCellSections
open GammaDefinableEuler GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaWeightedFamilies
open GammaIndicators GammaIteratedIntegral EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem integralFirst_from_euler (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    {n : ℕ} (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f)
    (y : Fin n → Values.Gamma (M := M)) (F : EulerFunction k (PaperGamma (M := M)))
    (he : ∀ a, f (Fin.cons a y) = F (toPaperGamma a)) :
    integralFirst h00 B k f hf y = totalEuler k F := by
  have hF : fibreFunction h00 B k f hf y = F := by
    apply eval_injective k
    funext x
    obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
    change fibreFunction h00 B k f hf y (toPaperGamma a) = F (toPaperGamma a)
    exact (fibreFunction_eval h00 B k f hf y a).trans (he a)
  exact congrArg (totalEuler k) hF

def graphCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) := {z | Fin.tail z ∈ C ∧ z 0 = T (Fin.tail z)}

theorem integrateFirst_graph (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hR : GammaDefinable B (graphCell C T)) :
    integrateFirst h00 hκ hs B hr hγ k n (indicatorFamily B (graphCell C T) hR) = indicatorFamily B C hC := by
  let f := indicatorFamily B (graphCell C T) hR
  have hf : IntegerFamilyDefinable B f.val := f.property
  apply Subtype.ext
  funext y
  change integralFirst h00 B k f.val hf y = (indicatorFamily B C hC).val y
  by_cases hy : y ∈ C
  · have he := integralFirst_from_euler h00 B k f.val hf y (point k (toPaperGamma (T y))) (by
      intro a
      by_cases ha : a = T y <;>
        simp [f, indicatorFamily, graphCell, hy, point_eval, toPaperGamma.injective.eq_iff, ha])
    exact he.trans (by simp [totalEuler_point, indicatorFamily, hy])
  · have he := integralFirst_from_euler h00 B k f.val hf y 0 (by
      intro a
      simp [f, indicatorFamily, graphCell, hy, eval_zero])
    exact he.trans (by simp [indicatorFamily, hy])

def bandCell {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) :
    Set (Fin (n + 1) → Values.Gamma (M := M)) :=
  {z | Fin.tail z ∈ C ∧ l (Fin.tail z) < z 0 ∧ z 0 < u (Fin.tail z)}

theorem integrateFirst_band (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
    (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hlu : ∀ y ∈ C, l y < u y) (hR : GammaDefinable B (bandCell C l u)) :
    integrateFirst h00 hκ hs B hr hγ k n (indicatorFamily B (bandCell C l u) hR) = -(indicatorFamily B C hC) := by
  let f := indicatorFamily B (bandCell C l u) hR
  have hf : IntegerFamilyDefinable B f.val := f.property
  apply Subtype.ext
  funext y
  change integralFirst h00 B k f.val hf y = -(indicatorFamily B C hC).val y
  by_cases hy : y ∈ C
  · have he := integralFirst_from_euler h00 B k f.val hf y
      (openInterval k (toPaperGamma (l y)) (toPaperGamma (u y))) (by
        intro a
        have hle : toPaperGamma (l y) < toPaperGamma a ↔ l y < a := Iff.rfl
        have hue : toPaperGamma a < toPaperGamma (u y) ↔ a < u y := Iff.rfl
        simp [f, indicatorFamily, bandCell, hy, openInterval_eval, hle, hue])
    have hlt : toPaperGamma (l y) < toPaperGamma (u y) := hlu y hy
    exact he.trans (by rw [totalEuler_openInterval, ite_eq_left hlt]; simp [indicatorFamily, hy])
  · have he := integralFirst_from_euler h00 B k f.val hf y 0 (by
      intro a
      simp [f, indicatorFamily, bandCell, hy, eval_zero])
    exact he.trans (by simp [indicatorFamily, hy])

end DiamondIntegral.Section4.GammaCellSections
