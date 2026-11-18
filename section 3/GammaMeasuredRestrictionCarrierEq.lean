import «section 3».GammaGroundMeasuredRVScissors
import «section 3».GammaGroundCarrierBijections

/-! Equal literal cut domains give an identity measured RV arrow with the
original structural volume and Gamma form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

def gammaMeasuredRestrictionCarrierEqHom (U : GammaGroundMeasuredRVObject hc B k)
    (X Y : GammaGroundDefSet hc B (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) (hY : Y.carrier ⊆ U.underlying.domain.carrier)
    (h : X.carrier = Y.carrier) : GammaGroundMeasuredRVHom (U.restrict X hX) (U.restrict Y hY) where
  bijection := GammaGroundBijection.ofCarrierEq h
  preserves _ := rfl

end DiamondIntegral.Section3
