import «section 5».CylindricalFibreSyntax
import «section 5».CylindricalEulerCertificates

/-! Relational fibre-shape certificates reconstruct actual cylindrical
Gamma cells. Their Euler values therefore follow from the checked integral. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaOrderLogic GammaCellSections GammaCellUnboundedSections

 def CylinderFibreKind.attach {n : ℕ} (k : CylinderFibreKind) (s : CylindricalShape n) :
    CylindricalShape (n + 1) :=
  match k with
  | .graph => .graph s
  | .band => .band s
  | .upperRay => .upperRay s
  | .lowerRay => .lowerRay s
  | .line => .line s

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem shaped_cell_of_fibre_certificate (B : Base (M := M)) {n : ℕ}
    (C : Set (Fin n → Values.Gamma (M := M))) (s : CylindricalShape n)
    (hC : ShapedGammaCell B n C s) (k : CylinderFibreKind)
    (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hprojection : ∀ z ∈ R, Fin.tail z ∈ C)
    (hshape : ∀ y ∈ C, k.Describes (fun t => Fin.cons t y ∈ R)) :
    ShapedGammaCell B (n + 1) R (k.attach s) := by
  have hex (y : Fin n → Values.Gamma (M := M)) :
      ∃ a : Fin k.endpoints → Values.Gamma (M := M),
        y ∈ C → k.ordered a ∧ ∀ t, Fin.cons t y ∈ R ↔ k.condition a t := by
    by_cases hy : y ∈ C
    · obtain ⟨a, ha, he⟩ := hshape y hy
      exact ⟨a, fun _ => ⟨ha, he⟩⟩
    · exact ⟨fun _ => 1, fun h => (hy h).elim⟩
  choose a ha using hex
  have hrow (z : Fin (n + 1) → Values.Gamma (M := M)) :
      z ∈ R ↔ Fin.tail z ∈ C ∧ k.condition (a (Fin.tail z)) (z 0) := by
    constructor
    · intro hz
      have hy := hprojection z hz
      refine ⟨hy, ((ha _ hy).2 (z 0)).mp ?_⟩
      simpa only [Fin.cons_self_tail] using hz
    · rintro ⟨hy, hz⟩
      simpa only [Fin.cons_self_tail] using ((ha _ hy).2 (z 0)).mpr hz
  cases k with
  | graph =>
    have he : R = graphCell C (fun y => a y 0) := by
      ext z
      exact hrow z
    subst R
    exact .graph hC _ hR
  | band =>
    have he : R = bandCell C (fun y => a y 0) (fun y => a y 1) := by
      ext z
      exact hrow z
    subst R
    exact .band hC _ _ (fun y hy => (ha y hy).1) hR
  | upperRay =>
    have he : R = upperRayCell C (fun y => a y 0) := by
      ext z
      exact hrow z
    subst R
    exact .upperRay hC _ hR
  | lowerRay =>
    have he : R = lowerRayCell C (fun y => a y 0) := by
      ext z
      exact hrow z
    subst R
    exact .lowerRay hC _ hR
  | line =>
    have he : R = lineCell C := by
      ext z
      simpa only [CylinderFibreKind.condition, and_true, lineCell, Set.mem_setOf_eq] using hrow z
    subst R
    exact .line hC hR

theorem ShapedGammaCell.fibre_certificate {B : Base (M := M)} {n : ℕ}
    {C : Set (Fin n → Values.Gamma (M := M))} {s : CylindricalShape n}
    (hC : ShapedGammaCell B n C s) (k : CylinderFibreKind)
    (a : (Fin n → Values.Gamma (M := M)) → Fin k.endpoints → Values.Gamma (M := M))
    (ho : ∀ y ∈ C, k.ordered (a y))
    (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (he : ∀ z, z ∈ R ↔ Fin.tail z ∈ C ∧ k.condition (a (Fin.tail z)) (z 0))
    (hR : GammaDefinable B R) : ShapedGammaCell B (n + 1) R (k.attach s) := by
  apply shaped_cell_of_fibre_certificate B C s hC k R hR
  · intro z hz
    exact (he z).mp hz |>.1
  · intro y hy
    refine ⟨a y, ho y hy, ?_⟩
    intro t
    simpa only [Fin.tail_cons, Fin.cons_zero, hy, true_and] using he (Fin.cons t y)

end DiamondIntegral.Section5
