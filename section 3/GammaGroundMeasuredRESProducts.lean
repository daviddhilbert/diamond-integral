import «section 3».GammaGroundMeasuredRESScissors
import «section 3».GammaGroundMeasuredRVSemiring

set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def GammaGroundMeasuredRESObject.product (U : GammaGroundMeasuredRESObject hc ground k)
    (V : GammaGroundMeasuredRESObject hc ground l) : GammaGroundMeasuredRESObject hc ground (k + l) :=
  ⟨U.obj.product V.obj, GammaGroundRVObject.product_res U.property V.property⟩

end DiamondIntegral.Section3
