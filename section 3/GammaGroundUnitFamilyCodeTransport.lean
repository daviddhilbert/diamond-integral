import «section 3».GammaGroundFamilyPieceValueMaps
import «section 3».RVUnitFullGammaCodes
import «section 3».GammaGroundGammaLiftReflection
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def GammaGroundGammaObject.unitCodeBijection (A : GammaGroundGammaObject hc B n) :
    GammaGroundFamilyBijection A.unitFamily A.codeLift :=
  GammaGroundFamilyBijection.pieces A.unitFamily (fun i => gammaGroundCodePreimage (A.piece i))
    (fun i => gammaGroundRVUnitFullCodeBijection (A.piece i))

theorem GammaGroundGammaObject.unitCode_decode (A : GammaGroundGammaObject hc B n) (u : A.unitFamily.Carrier) :
    A.decode (A.unitCodeBijection.equiv u) = A.unitValueFamilyMap.toFun u := by
  obtain ⟨i,u⟩ := u
  refine gammaGroundFamilyCarrier_ext A
    (a := A.decode (A.unitCodeBijection.equiv ⟨i,u⟩))
    (b := A.unitValueFamilyMap.toFun ⟨i,u⟩) ?_ ?_
  · rfl
  · exact gammaGroundRVUnitFullCode_decode (A.piece i) u

theorem GammaGroundGammaObject.unitCode_inverse_decode (A : GammaGroundGammaObject hc B n)
    (c : A.codeLift.Carrier) : A.decode c = A.unitValueFamilyMap.toFun (A.unitCodeBijection.equiv.symm c) := by
  have h := A.unitCode_decode (A.unitCodeBijection.equiv.symm c)
  rw [A.unitCodeBijection.equiv.apply_symm_apply] at h
  exact h

/-- Actual RV-object lift bijections retain all tags when transported
to full unit fibres. No generic descent assertion is used here. -/
def gammaGroundUnitFamilyBijectionOfRVLift {A D : GammaGroundGammaObject hc B n}
    (F : GammaGroundBijection A.rvLift.domain D.rvLift.domain) :
    GammaGroundFamilyBijection A.unitFamily D.unitFamily :=
  D.unitCodeBijection.symm.comp ((gammaGroundGammaCodeBijectionOfLift F).comp A.unitCodeBijection)

/-- A genuinely contracting full RV family lift is precisely the witness
required by the intended Gamma-category definition. -/
def gammaGroundGammaHomOfUnitFamilyLift {A D : GammaGroundGammaObject hc B n}
    (H : GammaGroundFamilyBijection A D) (L : GammaGroundFamilyBijection A.unitFamily D.unitFamily)
    (hL : ∀ u, D.unitValueFamilyMap.toFun (L.equiv u) = H.equiv (A.unitValueFamilyMap.toFun u)) :
    GammaGroundGammaHom A D where
  bijection := H
  contraction := by
    let C := D.unitCodeBijection.comp (L.comp A.unitCodeBijection.symm)
    refine ⟨C,fun c => ?_⟩
    have h := hL (A.unitCodeBijection.equiv.symm c)
    exact (D.unitCode_decode (L.equiv (A.unitCodeBijection.equiv.symm c))).trans
      (h.trans (congrArg H.equiv (A.unitCode_inverse_decode c).symm))

end DiamondIntegral.Section3
