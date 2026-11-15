import «section 4».GammaConstructedCellEuler

/-! Finite syntactic cell shapes compute both Euler theories. In
particular the bounded Euler integer has a finite certificate supplied
by an actual cylindrical decomposition over the original parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
open GammaOrderLogic GammaCylindricalCells GammaCellSections GammaCellUnboundedSections
open GammaIntegerFamilies GammaWeightedFamilies GammaIndicators GammaIteratedIntegral GammaCylindricalDecompositionData

inductive CylindricalShape : ℕ → Type where
  | base : CylindricalShape 0
  | graph {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1)
  | band {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1)
  | upperRay {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1)
  | lowerRay {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1)
  | line {n : ℕ} : CylindricalShape n → CylindricalShape (n + 1)

def CylindricalShape.eulerValue (k : EulerKind) : {n : ℕ} → CylindricalShape n → ℤ
  | _, .base => 1
  | _, .graph s => s.eulerValue k
  | _, .band s => -s.eulerValue k
  | _, .upperRay s => k.rayValue * s.eulerValue k
  | _, .lowerRay s => k.rayValue * s.eulerValue k
  | _, .line s => k.lineValue * s.eulerValue k

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive ShapedGammaCell (B : Base (M := M)) :
    (n : ℕ) → Set (Fin n → Values.Gamma (M := M)) → CylindricalShape n → Prop where
  | base : ShapedGammaCell B 0 Set.univ .base
  | graph {n C s} (hc : ShapedGammaCell B n C s)
      (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hR : GammaDefinable B (graphCell C T)) :
      ShapedGammaCell B (n + 1) (graphCell C T) (.graph s)
  | band {n C s} (hc : ShapedGammaCell B n C s)
      (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hlu : ∀ y ∈ C, l y < u y) (hR : GammaDefinable B (bandCell C l u)) :
      ShapedGammaCell B (n + 1) (bandCell C l u) (.band s)
  | upperRay {n C s} (hc : ShapedGammaCell B n C s)
      (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hR : GammaDefinable B (upperRayCell C l)) :
      ShapedGammaCell B (n + 1) (upperRayCell C l) (.upperRay s)
  | lowerRay {n C s} (hc : ShapedGammaCell B n C s)
      (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
      (hR : GammaDefinable B (lowerRayCell C u)) :
      ShapedGammaCell B (n + 1) (lowerRayCell C u) (.lowerRay s)
  | line {n C s} (hc : ShapedGammaCell B n C s) (hR : GammaDefinable B (lineCell C)) :
      ShapedGammaCell B (n + 1) (lineCell C) (.line s)

theorem gamma_cell_has_shape {B : Base (M := M)} {n d : ℕ}
    {C : Set (Fin n → Values.Gamma (M := M))} (h : Cell B n C d) :
    ∃ s : CylindricalShape n, ShapedGammaCell B n C s := by
  induction h with
  | base => exact ⟨.base, .base⟩
  | graph h T hR ih => obtain ⟨s, hs⟩ := ih; exact ⟨.graph s, .graph hs T hR⟩
  | band h l u hlu hR ih => obtain ⟨s, hs⟩ := ih; exact ⟨.band s, .band hs l u hlu hR⟩
  | upperRay h l hR ih => obtain ⟨s, hs⟩ := ih; exact ⟨.upperRay s, .upperRay hs l hR⟩
  | lowerRay h u hR ih => obtain ⟨s, hs⟩ := ih; exact ⟨.lowerRay s, .lowerRay hs u hR⟩
  | line h hR ih => obtain ⟨s, hs⟩ := ih; exact ⟨.line s, .line hs hR⟩

theorem ShapedGammaCell.definable {B : Base (M := M)} {n : ℕ} {s : CylindricalShape n}
    {C : Set (Fin n → Values.Gamma (M := M))} (h : ShapedGammaCell B n C s) : GammaDefinable B C := by
  cases h with
  | base => exact univ_definable_base B 0
  | graph _ _ hR => exact hR
  | band _ _ _ _ hR => exact hR
  | upperRay _ _ hR => exact hR
  | lowerRay _ _ hR => exact hR
  | line _ hR => exact hR

theorem shaped_cell_euler_value (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    {n : ℕ} {s : CylindricalShape n} {C : Set (Fin n → Values.Gamma (M := M))}
    (h : ShapedGammaCell B n C s) :
    integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B C h.definable) = s.eulerValue k := by
  induction h with
  | base => simp [integrateAll, evaluateZero, indicatorFamily, CylindricalShape.eulerValue]
  | @graph n C s h T hR ih =>
    change integrateAll h00 hκ hs B hr hγ k n (integrateFirst h00 hκ hs B hr hγ k n _) = _
    rw [integrateFirst_graph h00 hκ hs B hr hγ k C h.definable T hR]
    exact ih
  | @band n C s h l u hlu hR ih =>
    change integrateAll h00 hκ hs B hr hγ k n (integrateFirst h00 hκ hs B hr hγ k n _) = _
    rw [integrateFirst_band h00 hκ hs B hr hγ k C h.definable l u hlu hR, map_neg, ih]
    rfl
  | @upperRay n C s h l hR ih =>
    change integrateAll h00 hκ hs B hr hγ k n (integrateFirst h00 hκ hs B hr hγ k n _) = _
    rw [integrateFirst_upperRay h00 hκ hs B hr hγ k C h.definable l hR, map_zsmul, ih]
    rfl
  | @lowerRay n C s h u hR ih =>
    change integrateAll h00 hκ hs B hr hγ k n (integrateFirst h00 hκ hs B hr hγ k n _) = _
    rw [integrateFirst_lowerRay h00 hκ hs B hr hγ k C h.definable u hR, map_zsmul, ih]
    rfl
  | @line n C s h hR ih =>
    change integrateAll h00 hκ hs B hr hγ k n (integrateFirst h00 hκ hs B hr hγ k n _) = _
    rw [integrateFirst_line h00 hκ hs B hr hγ k C h.definable hR, map_zsmul, ih]
    rfl

theorem finite_cylindrical_euler_certificate (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (n : ℕ) (X : Set (Fin n → Values.Gamma (M := M))) (hX : GammaDefinable B X) :
    ∃ D : Decomposition B n X, ∃ shape : Fin D.size → CylindricalShape n,
      (∀ i, ShapedGammaCell B n (D.pieces i) (shape i)) ∧
      ∀ k : EulerKind, integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B X hX) =
        ∑ i, (shape i).eulerValue k := by
  obtain ⟨D⟩ := GammaCylindricalDecompositionExistence.exists_decomposition h00 hκ hs B hr hγ n X hX
  choose shape hshape using (fun i => gamma_cell_has_shape (D.cells i))
  refine ⟨D, shape, hshape, ?_⟩
  intro k
  have hp := GammaFinitePartitions.integral_partition h00 hκ hs B hr hγ k n X hX D.pieces
    (fun i => (hshape i).definable) D.disjoint D.cover
  exact hp.trans (Finset.sum_congr rfl (fun i _ => shaped_cell_euler_value h00 hκ hs B hr hγ k (hshape i)))

end DiamondIntegral.Section5
