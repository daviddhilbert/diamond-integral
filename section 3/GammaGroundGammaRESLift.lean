import «section 3».GammaGroundGammaRVLift
import «section 3».GammaGroundRVFamilySupport
/-! Finite Gamma objects lift to the full RES subcategory: support is
measured on the entire tagged RV source, including its zero tags. -/

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

theorem GammaGroundGammaObject.rvLift_res (A : GammaGroundGammaObject hc ground k) (hA : gammaGroundFiniteGammaProperty A) :
    gammaGroundResProperty A.rvLift :=
  A.rvPieces.rvObject_res A.rvPieces_nonzero (fun i => gammaGroundGammaRVCodeLift_res (A.piece i) (hA i))

def GammaGroundFiniteGammaObject.resLift (A : GammaGroundFiniteGammaObject hc ground k) : GammaGroundRESObject hc ground k :=
  ⟨A.obj.rvLift, A.obj.rvLift_res A.property⟩

theorem gammaGroundFiniteGammaHom_lift_iso {A B : GammaGroundFiniteGammaObject hc ground k} (f : A ⟶ B) :
    Nonempty (A.resLift ≅ B.resLift) := by
  obtain ⟨e⟩ := gammaGroundGammaHom_lift_iso f.hom
  exact ⟨(gammaGroundResProperty (hc := hc) (ground := ground) (k := k)).isoMk e⟩

end DiamondIntegral.Section3
