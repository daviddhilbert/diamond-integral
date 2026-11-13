import «section 3».GammaGroundBijections

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
variable {Q : Space LRV M} {A B : GammaGroundDefSet hc ground Q}

def GammaGroundBijection.ofCarrierEq (h : A.carrier = B.carrier) : GammaGroundBijection A B where
  map := GammaGroundMap.inclusion h.le
  bijective := by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun z : B => z.val) he)
    · intro b
      exact ⟨⟨b.val, h.ge b.property⟩, rfl⟩

end DiamondIntegral.Section3
