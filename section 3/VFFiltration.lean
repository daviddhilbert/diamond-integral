import «section 3».VFScissors
import «section 3».VFSemiring

/-! The fixed-degree VF positive quotients form the actual dimension
filtration. Raising a bound retains the original domain and bijections. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [TopologicalSpace (Section2.VF M)] {S : Set M} {k l m : ℕ}

def vfRaiseKPlus (hkl : k ≤ l) : VFKPlus (M := M) S k →+ VFKPlus S l :=
  PositiveAdditiveGrothendieck.lift (vfPresentation S k) {
    toFun U := vfClass (U.raise hkl)
    iso := by
      intro U V h
      obtain ⟨e⟩ := h
      exact vfClass_iso (asIso (show U.raise hkl ⟶ V.raise hkl from e.hom))
    empty := vfClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      exact positiveClass_scissor (vfPresentation S l) ⟨U.raise hkl, X, hX, rfl, rfl, rfl, rfl⟩ }

@[simp] theorem vfRaiseKPlus_class (hkl : k ≤ l) (U : VFObject (M := M) S k) :
    vfRaiseKPlus hkl (vfClass U) = vfClass (U.raise hkl) := PositiveAdditiveGrothendieck.lift_of _ _ U

theorem vfRaiseKPlus_refl : vfRaiseKPlus (M := M) (S := S) (le_refl k) = AddMonoidHom.id _ := by
  apply PositiveAdditiveGrothendieck.hom_ext (vfPresentation S k)
  intro U
  exact vfRaiseKPlus_class (le_refl k) U

theorem vfRaiseKPlus_comp (hkl : k ≤ l) (hlm : l ≤ m) :
    (vfRaiseKPlus (M := M) (S := S) hlm).comp (vfRaiseKPlus hkl) = vfRaiseKPlus (hkl.trans hlm) := by
  apply PositiveAdditiveGrothendieck.hom_ext (vfPresentation S k)
  intro U
  change vfRaiseKPlus hlm (vfRaiseKPlus hkl (vfClass U)) = vfRaiseKPlus (hkl.trans hlm) (vfClass U)
  rw [vfRaiseKPlus_class, vfRaiseKPlus_class, vfRaiseKPlus_class]
  rfl

end DiamondIntegral.Section3
