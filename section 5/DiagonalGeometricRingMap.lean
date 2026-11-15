import «section 5».DiagonalGeometricProducts
import «section 5».DiagonalGeometricBijections
import «section 5».DiagonalGeometricUnit
import «section 5».RESRawComparisonEquivalence

/-! The forward geometric comparison is an actual ring homomorphism.
The native RES composite retains the explicit original Puiseux-model
hypothesis of the native residue comparison. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical

open PuiseuxOriginal.DiagonalConstructible

def PuiseuxOriginal.DiagonalConstructible.geometricInvariant : Invariant EquivariantVariety.Ring where
  value := geometricValue
  unit := geometricValue_unit
  product := geometricValue_product
  iso := fun _ _ f => geometricValue_iso f
  empty := geometricValue_empty
  scissor := geometricValue_scissor

def PuiseuxOriginal.DiagonalConstructible.toVarietyRing : Ring →+* EquivariantVariety.Ring := lift geometricInvariant

theorem PuiseuxOriginal.DiagonalConstructible.toVarietyRing_objectClass (X : Object) : toVarietyRing (objectClass X) = geometricValue X :=
  lift_objectClass geometricInvariant X


open PuiseuxOriginal
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section4
local instance nativeGeometricStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

def PuiseuxOriginal.nativeToVarietyRing : RESDimensionFreeRing.Ring originalPuiseuxGround →+* EquivariantVariety.Ring :=
  DiagonalConstructible.toVarietyRing.comp rawRESComparison.toRingHom

theorem PuiseuxOriginal.nativeToVarietyRing_comparison (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    nativeToVarietyRing x = DiagonalConstructible.toVarietyRing (rawRESComparison x) := rfl

end DiamondIntegral.Section5
