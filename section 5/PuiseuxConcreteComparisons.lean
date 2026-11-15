import «section 5».PuiseuxConcreteModel
import «section 5».GeometricTheta
import «section 5».PuiseuxInducedRV

/-! The actual original-language comparison on the concrete complex
Puiseux model. Its ACVF-model hypothesis is discharged by the checked
Newton–Puiseux and quotient-language constructions. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section4
local instance concreteStructure : LRV.Structure Carrier := canonicalInterpret
local instance concreteModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

def canonicalModelPresentation_concrete : PuiseuxModelPresentation Carrier := canonicalModelPresentation

def theta_5_14_concrete :
    RESDimensionFreeReduction.Ring originalPuiseuxGround ≃+* EquivariantVariety.ModifiedRing := theta_5_14

theorem theta_5_14_concrete_mk (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround x) =
      Ideal.Quotient.mk EquivariantVariety.linearActionIdeal (rawVarietyComparison x) := rfl

end DiamondIntegral.Section5.PuiseuxOriginal
