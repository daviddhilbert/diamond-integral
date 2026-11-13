import «section 4».GammaCellUnboundedSections

/-! Geometric Euler values for actual cylindrical graph/interval cells.
The dimension records graph versus interval steps. The formula applies to
ordinary o-minimal cells after supplying their cylindrical witnesses; no
cell-decomposition existence theorem is assumed or proved in this file. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCylindricalCells
open GammaOrderLogic GammaIntegerFamilies GammaWeightedFamilies GammaIndicators GammaIteratedIntegral
open GammaCellSections GammaCellUnboundedSections

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive Cell (B : Base (M := M)) : (n : ℕ) → Set (Fin n → Values.Gamma (M := M)) → ℕ → Prop where
  | base : Cell B 0 Set.univ 0
  | graph {n d C} (hc : Cell B n C d)
      (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hR : GammaDefinable B (graphCell C T)) : Cell B (n + 1) (graphCell C T) d
  | band {n d C} (hc : Cell B n C d)
      (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hlu : ∀ y ∈ C, l y < u y) (hR : GammaDefinable B (bandCell C l u)) :
      Cell B (n + 1) (bandCell C l u) (d + 1)
  | upperRay {n d C} (hc : Cell B n C d)
      (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hR : GammaDefinable B (upperRayCell C l)) : Cell B (n + 1) (upperRayCell C l) (d + 1)
  | lowerRay {n d C} (hc : Cell B n C d)
      (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hR : GammaDefinable B (lowerRayCell C u)) : Cell B (n + 1) (lowerRayCell C u) (d + 1)
  | line {n d C} (hc : Cell B n C d) (hR : GammaDefinable B (lineCell C)) :
      Cell B (n + 1) (lineCell C) (d + 1)

theorem Cell.definable {B : Base (M := M)} {n d : ℕ} {C : Set (Fin n → Values.Gamma (M := M))}
    (hc : Cell B n C d) : GammaDefinable B C := by
  cases hc with
  | base => exact univ_definable_base B 0
  | graph _ _ hR => exact hR
  | band _ _ _ _ hR => exact hR
  | upperRay _ _ hR => exact hR
  | lowerRay _ _ hR => exact hR
  | line _ hR => exact hR

theorem geometric_value (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n d : ℕ} {C : Set (Fin n → Values.Gamma (M := M))} (hc : Cell B n C d) :
    integrateAll h00 hκ hs B hr hγ EulerKind.geometric n (indicatorFamily B C hc.definable) = (-1 : ℤ) ^ d := by
  induction hc with
  | base => simp [integrateAll, evaluateZero, indicatorFamily]
  | @graph n d C hc T hR ih =>
    change integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
      (integrateFirst h00 hκ hs B hr hγ EulerKind.geometric n _) = _
    rw [integrateFirst_graph h00 hκ hs B hr hγ EulerKind.geometric C hc.definable T hR]
    exact ih
  | @band n d C hc l u hlu hR ih =>
    change integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
      (integrateFirst h00 hκ hs B hr hγ EulerKind.geometric n _) = _
    rw [integrateFirst_band h00 hκ hs B hr hγ EulerKind.geometric C hc.definable l u hlu hR, map_neg, ih,
      pow_succ]
    ring
  | @upperRay n d C hc l hR ih =>
    change integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
      (integrateFirst h00 hκ hs B hr hγ EulerKind.geometric n _) = _
    rw [integrateFirst_upperRay h00 hκ hs B hr hγ EulerKind.geometric C hc.definable l hR, map_zsmul, ih,
      pow_succ]
    simp [EulerKind.rayValue]
  | @lowerRay n d C hc u hR ih =>
    change integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
      (integrateFirst h00 hκ hs B hr hγ EulerKind.geometric n _) = _
    rw [integrateFirst_lowerRay h00 hκ hs B hr hγ EulerKind.geometric C hc.definable u hR, map_zsmul, ih,
      pow_succ]
    simp [EulerKind.rayValue]
  | @line n d C hc hR ih =>
    change integrateAll h00 hκ hs B hr hγ EulerKind.geometric n
      (integrateFirst h00 hκ hs B hr hγ EulerKind.geometric n _) = _
    rw [integrateFirst_line h00 hκ hs B hr hγ EulerKind.geometric C hc.definable hR, map_zsmul, ih, pow_succ]
    simp [EulerKind.lineValue]

end DiamondIntegral.Section4.GammaCylindricalCells
