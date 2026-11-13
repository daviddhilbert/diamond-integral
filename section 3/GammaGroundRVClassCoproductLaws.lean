import «section 3».GammaGroundRVIsomorphismClasses

/-! Coproduct operations on actual RV objects respect isomorphisms.
The class-isomorphism comparison supplies concrete bijections. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundRVCoprodIso {U U' V V' : GammaGroundRVObject hc ground k} (f : U ≅ U') (g : V ≅ V') :
    Nonempty (U.coprod V ≅ U'.coprod V') := by
  apply gammaGroundRVClass_eq_iff_iso.mp
  rw [gammaGroundRVClass_coprod, gammaGroundRVClass_coprod, gammaGroundRVClass_iso f, gammaGroundRVClass_iso g]

theorem gammaGroundRVCoprod_assoc (U V W : GammaGroundRVObject hc ground k) :
    Nonempty ((U.coprod V).coprod W ≅ U.coprod (V.coprod W)) := by
  apply gammaGroundRVClass_eq_iff_iso.mp
  simp only [gammaGroundRVClass_coprod, add_assoc]

theorem gammaGroundRVCoprod_comm (U V : GammaGroundRVObject hc ground k) : Nonempty (U.coprod V ≅ V.coprod U) := by
  apply gammaGroundRVClass_eq_iff_iso.mp
  simp only [gammaGroundRVClass_coprod, add_comm]

theorem gammaGroundRVCoprod_empty (U : GammaGroundRVObject hc ground k) :
    Nonempty ((GammaGroundRVObject.empty hc ground k).coprod U ≅ U) := by
  apply gammaGroundRVClass_eq_iff_iso.mp
  rw [gammaGroundRVClass_coprod, gammaGroundRVClass_empty, zero_add]

end DiamondIntegral.Section3
