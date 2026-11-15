import «section 5».RESCharacterQuotient
import «section 5».DiagonalAffineSpaces

/-! The reduced native RES ring is identified with the actual diagonal
constructible ring modulo all linear-action relations with arbitrary
equivariant factors. The comparison to geometric varieties is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section4
local instance resLinearActionQuotientStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

theorem fibreIdeal_image_eq_linearActionIdeal :
    Ideal.map rawRESComparison.toRingHom (RESDimensionFreeReduction.fibreIdeal originalPuiseuxGround) =
      DiagonalConstructible.linearActionIdeal :=
  fibreIdeal_image_eq_lineIdeal.trans DiagonalConstructible.linearActionIdeal_eq_lineIdeal.symm

def reducedLinearActionRing := DiagonalConstructible.Ring ⧸ DiagonalConstructible.linearActionIdeal
  deriving CommRing

def residueLinearActionComparison : RESDimensionFreeReduction.Ring originalPuiseuxGround ≃+* reducedLinearActionRing :=
  Ideal.quotientEquiv (RESDimensionFreeReduction.fibreIdeal originalPuiseuxGround)
    DiagonalConstructible.linearActionIdeal rawRESComparison fibreIdeal_image_eq_linearActionIdeal.symm

theorem residueLinearActionComparison_mk (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    residueLinearActionComparison (RESDimensionFreeReduction.quotient originalPuiseuxGround x) =
      Ideal.Quotient.mk DiagonalConstructible.linearActionIdeal (rawRESComparison x) := rfl

end DiamondIntegral.Section5.PuiseuxOriginal
