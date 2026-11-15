import «section 5».GeometricLinearIdeals

/-! The actual geometric quotient comparison. The native source retains
the explicitly recorded ACVF hypothesis on the concrete Puiseux structure. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open PuiseuxOriginal

def EquivariantVariety.ModifiedRing :=
  EquivariantVariety.Ring ⧸ EquivariantVariety.linearActionIdeal
  deriving CommRing

def PuiseuxOriginal.DiagonalConstructible.geometricLinearActionComparison :
    reducedLinearActionRing ≃+* EquivariantVariety.ModifiedRing :=
  Ideal.quotientEquiv DiagonalConstructible.linearActionIdeal EquivariantVariety.linearActionIdeal
    DiagonalConstructible.rawGeometricComparison geometric_linearActionIdeal_correspondence.symm

theorem PuiseuxOriginal.DiagonalConstructible.geometricLinearActionComparison_mk
    (x : DiagonalConstructible.Ring) :
    geometricLinearActionComparison (Ideal.Quotient.mk DiagonalConstructible.linearActionIdeal x) =
      Ideal.Quotient.mk EquivariantVariety.linearActionIdeal (DiagonalConstructible.toVarietyRing x) := rfl

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section4
local instance geometricThetaStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

def PuiseuxOriginal.theta_5_14 :
    RESDimensionFreeReduction.Ring originalPuiseuxGround ≃+* EquivariantVariety.ModifiedRing :=
  residueLinearActionComparison.trans DiagonalConstructible.geometricLinearActionComparison

theorem PuiseuxOriginal.theta_5_14_mk (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    theta_5_14 (RESDimensionFreeReduction.quotient originalPuiseuxGround x) =
      Ideal.Quotient.mk EquivariantVariety.linearActionIdeal (rawVarietyComparison x) := rfl

end DiamondIntegral.Section5
