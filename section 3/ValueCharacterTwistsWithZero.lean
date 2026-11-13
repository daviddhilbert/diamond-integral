import «section 3».ValueCharacterTwists
import Mathlib.Algebra.GroupWithZero.WithZero
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {G : Type*} [GroupWithZero G]

def unitsEquivExtendZero (e : Gˣ ≃* Gˣ) : G ≃* G := by
  classical
  exact WithZero.withZeroUnitsEquiv.symm.trans
    ((MulEquiv.withZero e).trans WithZero.withZeroUnitsEquiv)

@[simp] theorem unitsEquivExtendZero_coe (e : Gˣ ≃* Gˣ) (u : Gˣ) :
    unitsEquivExtendZero e (u : G) = (e u : G) := by
  classical
  change WithZero.withZeroUnitsEquiv
    (MulEquiv.withZero e (WithZero.withZeroUnitsEquiv.symm (u : G))) = _
  rw [WithZero.withZeroUnitsEquiv_symm_apply_coe]
  rfl

@[simp] theorem unitsEquivExtendZero_zero (e : Gˣ ≃* Gˣ) :
    unitsEquivExtendZero e 0 = 0 := by
  exact map_zero (unitsEquivExtendZero e)

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvOriginalGroundCharacterTwistZero (B : Base (M := M))
    (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ) :
    CanonicalRV.RVSort M ≃* CanonicalRV.RVSort M :=
  unitsEquivExtendZero (rvOriginalGroundCharacterTwist B χ)

@[simp] theorem rvOriginalGroundCharacterTwistZero_coe (B : Base (M := M))
    (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)
    (u : (CanonicalRV.RVSort M)ˣ) :
    rvOriginalGroundCharacterTwistZero B χ (u : CanonicalRV.RVSort M) =
      (rvOriginalGroundCharacterTwist B χ u : CanonicalRV.RVSort M) :=
  unitsEquivExtendZero_coe _ _

theorem rvOriginalGroundCharacterTwistZero_value (B : Base (M := M))
    (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)
    (u : CanonicalRV.RVSort M) :
    Values.vrv (rvOriginalGroundCharacterTwistZero B χ u) = Values.vrv u := by
  by_cases hu : u = 0
  · subst u
    rw [rvOriginalGroundCharacterTwistZero,unitsEquivExtendZero_zero]
  · let t := Units.mk0 u hu
    have ht : (t : CanonicalRV.RVSort M) = u := rfl
    rw [← ht,rvOriginalGroundCharacterTwistZero_coe]
    exact congrArg Subtype.val (rvOriginalGroundCharacterTwist_value B χ t)

end DiamondIntegral.Section3
