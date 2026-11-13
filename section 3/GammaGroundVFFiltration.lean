import «section 3».GammaGroundVFScissors
import «section 3».GammaGroundFiniteVFScissors

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l m : ℕ}

def gammaGroundVFRaiseKPlus (hkl : k ≤ l) : GammaGroundVFKPlus hc ground k →+ GammaGroundVFKPlus hc ground l :=
  PositiveAdditiveGrothendieck.lift (gammaGroundVFPresentation hc ground k) {
    toFun U := gammaGroundVFClass (U.raise hkl)
    iso := by
      rintro U V ⟨e⟩
      exact gammaGroundVFClass_iso (asIso (show U.raise hkl ⟶ V.raise hkl from e.hom))
    empty := gammaGroundVFClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      exact positiveClass_scissor (gammaGroundVFPresentation hc ground l)
        ⟨U.raise hkl, X, hX, rfl, rfl, rfl, rfl⟩ }

@[simp] theorem gammaGroundVFRaiseKPlus_class (hkl : k ≤ l) (U : GammaGroundVFObject hc ground k) :
    gammaGroundVFRaiseKPlus hkl (gammaGroundVFClass U) = gammaGroundVFClass (U.raise hkl) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaGroundVFRaiseKPlus_refl :
    gammaGroundVFRaiseKPlus (hc := hc) (ground := ground) (le_refl k) = AddMonoidHom.id _ := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundVFPresentation hc ground k)
  intro U
  exact gammaGroundVFRaiseKPlus_class (le_refl k) U

theorem gammaGroundVFRaiseKPlus_comp (hkl : k ≤ l) (hlm : l ≤ m) :
    (gammaGroundVFRaiseKPlus (hc := hc) (ground := ground) hlm).comp (gammaGroundVFRaiseKPlus hkl) =
      gammaGroundVFRaiseKPlus (hkl.trans hlm) := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundVFPresentation hc ground k)
  intro U
  change gammaGroundVFRaiseKPlus hlm (gammaGroundVFRaiseKPlus hkl (gammaGroundVFClass U)) =
    gammaGroundVFRaiseKPlus (hkl.trans hlm) (gammaGroundVFClass U)
  rw [gammaGroundVFRaiseKPlus_class, gammaGroundVFRaiseKPlus_class, gammaGroundVFRaiseKPlus_class]
  rfl

def gammaGroundVFToFiniteKPlus : GammaGroundVFKPlus hc ground k →+ GammaGroundFiniteVFKPlus hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundVFPresentation hc ground k) {
    toFun U := gammaGroundFiniteVFClass (.ofBound U)
    iso := by
      rintro U V ⟨e⟩
      exact gammaGroundFiniteVFClass_iso (asIso (show GammaGroundFiniteVFObject.ofBound U ⟶ .ofBound V from e.hom))
    empty := gammaGroundFiniteVFClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      exact positiveClass_scissor (gammaGroundFiniteVFPresentation hc ground)
        ⟨GammaGroundFiniteVFObject.ofBound U, X, hX, rfl, rfl, rfl, rfl⟩ }

@[simp] theorem gammaGroundVFToFiniteKPlus_class (U : GammaGroundVFObject hc ground k) :
    gammaGroundVFToFiniteKPlus (gammaGroundVFClass U) = gammaGroundFiniteVFClass (.ofBound U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaGroundVFToFiniteKPlus_raise (hkl : k ≤ l) :
    (gammaGroundVFToFiniteKPlus (hc := hc) (ground := ground) (k := l)).comp (gammaGroundVFRaiseKPlus hkl) =
      (gammaGroundVFToFiniteKPlus : GammaGroundVFKPlus hc ground k →+ _) := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaGroundVFPresentation hc ground k)
  intro U
  change gammaGroundVFToFiniteKPlus (gammaGroundVFRaiseKPlus hkl (gammaGroundVFClass U)) =
    gammaGroundVFToFiniteKPlus (gammaGroundVFClass U)
  rw [gammaGroundVFRaiseKPlus_class, gammaGroundVFToFiniteKPlus_class, gammaGroundVFToFiniteKPlus_class]
  rfl

end DiamondIntegral.Section3
