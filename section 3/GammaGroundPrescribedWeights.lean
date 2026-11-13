import «section 3».GammaGroundRVLabelValues
import «section 3».GammaGroundInverseForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

/-- A definable prescribed combined weight determines an actual volume
form for any finite RV label, including in degree zero. -/
def GammaGroundRVObject.withCombinedWeight (U : GammaGroundRVObject hc B k)
    (w : GammaGroundVolumeForm hc B U.domain) : GammaGroundMeasuredRVObject hc B k :=
  ⟨U,w.mul U.labelWeightForm.inv⟩

theorem GammaGroundRVObject.withCombinedWeight_value (U : GammaGroundRVObject hc B k)
    (w : GammaGroundVolumeForm hc B U.domain) (a : U.domain) :
    (U.withCombinedWeight w).combinedWeight a = gammaGroundFormValue w a := by
  change gammaGroundFormValue (w.mul U.labelWeightForm.inv) a * _ = _
  rw [GammaGroundVolumeForm.mul_value,GammaGroundVolumeForm.inv_value,U.labelWeightForm_value]
  exact inv_mul_cancel_right _ _

def GammaGroundRESObject.withCombinedWeight (U : GammaGroundRESObject hc B k)
    (w : GammaGroundVolumeForm hc B U.obj.domain) : GammaGroundMeasuredRESObject hc B k :=
  ⟨U.obj.withCombinedWeight w,U.property⟩
end DiamondIntegral.Section3
