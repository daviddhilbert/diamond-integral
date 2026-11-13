import «section 3».GammaGroundRealization
import «section 3».GammaGroundMaps

/-! Sets and the complete graph of a Gamma-ground map have a common
small real interpretation without changing the VF coefficient field. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

theorem GammaGroundMap.realize {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hS : Cardinal.mk ground.real < κ) :
    ∃ T : Set M, ground.real ⊆ T ∧ Cardinal.mk T < κ ∧
      vfParameterField T = vfParameterField ground.real ∧
      ∃ hA : Q.Definable T A.carrier, ∃ hB : R.Definable T B.carrier,
        (Q.prod R).Definable T {z | ∃ a : A, a.val = z.1 ∧ (f a).val = z.2} := by
  let P : Fin 3 → Space LRV M := ![Q, R, Q.prod R]
  let D : ∀ i, Set (P i).Carrier :=
    Fin.cases A.carrier (Fin.cases B.carrier
      (Fin.cases {z | ∃ a : A, a.val = z.1 ∧ (f a).val = z.2} (fun i => i.elim0)))
  have hD : ∀ i, GammaGroundDefinable hc ground (P i) (D i) := by
    intro i
    fin_cases i
    · exact A.definable
    · exact B.definable
    · exact f.graph_definable
  obtain ⟨T, hT, hs, hf, hd⟩ := GammaGroundDefinable.realizeFinite P D hD hκ hS
  exact ⟨T, hT, hs, hf, hd 0, hd 1, hd 2⟩

end DiamondIntegral.Section3
