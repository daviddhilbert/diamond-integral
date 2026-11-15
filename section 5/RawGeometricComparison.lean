import «section 5».GeometricInverseRingMap
import «section 5».DiagonalPresentationPartitions

/-! Both composition identities for the actual geometric comparison.
The native RES equivalence retains its explicit original Puiseux-model
hypothesis; the constructible/geometric equivalence is unconditional. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem toDiagonalRing_geometricValue (X : DiagonalConstructible.Object) :
    EquivariantVariety.toDiagonalRing (DiagonalConstructible.geometricValue X) =
      DiagonalConstructible.objectClass X := by
  let c := Classical.choice (invariant_constructible_immersed_presentation (rationalAffineObject X.weights)
    (complexSpectrumExtension X.domain X.definable) (complexSpectrumExtension_constructible _ _)
    (complexSpectrumExtension_invariant _ _ _ X.invariant))
  letI := c.finite
  letI (i : c.index) := c.immersion i
  have hC : DiagonalConstructible.geometricValue X = c.value := constructibleClass_eq_presentation _ _ _ _ c
  rw [hC]
  change EquivariantVariety.toDiagonalRing (∑ i, EquivariantVariety.objectClass (c.piece i)) = _
  rw [map_sum]
  simp only [EquivariantVariety.toDiagonalRing_objectClass]
  have hi (i : c.index) : geometricPreimage (c.piece i) =
      DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject X.weights (c.inclusion i)) :=
    geometricPreimage_of_immersion X.weights (c.inclusion i)
  simp_rw [hi]
  exact (diagonalObject_presentation_partition X c).symm

theorem toVarietyRing_toDiagonalRing :
    DiagonalConstructible.toVarietyRing.comp EquivariantVariety.toDiagonalRing =
      RingHom.id EquivariantVariety.Ring := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro X
  change DiagonalConstructible.toVarietyRing (EquivariantVariety.toDiagonalRing (EquivariantVariety.objectClass X)) =
    EquivariantVariety.objectClass X
  rw [EquivariantVariety.toDiagonalRing_objectClass]
  exact toVarietyRing_geometricPreimage X

theorem toDiagonalRing_toVarietyRing :
    EquivariantVariety.toDiagonalRing.comp DiagonalConstructible.toVarietyRing =
      RingHom.id DiagonalConstructible.Ring := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro X
  change EquivariantVariety.toDiagonalRing (DiagonalConstructible.toVarietyRing (DiagonalConstructible.objectClass X)) =
    DiagonalConstructible.objectClass X
  rw [DiagonalConstructible.toVarietyRing_objectClass]
  exact toDiagonalRing_geometricValue X

def PuiseuxOriginal.DiagonalConstructible.rawGeometricComparison :
    DiagonalConstructible.Ring ≃+* EquivariantVariety.Ring :=
  RingEquiv.ofRingHom DiagonalConstructible.toVarietyRing EquivariantVariety.toDiagonalRing
    toVarietyRing_toDiagonalRing toDiagonalRing_toVarietyRing

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open DiamondIntegral.Section4
local instance rawGeometricStructure : LRV.Structure Carrier := canonicalInterpret
variable [Carrier ⊨ Axioms.ACVF]

def PuiseuxOriginal.rawVarietyComparison :
    RESDimensionFreeRing.Ring originalPuiseuxGround ≃+* EquivariantVariety.Ring :=
  rawRESComparison.trans DiagonalConstructible.rawGeometricComparison

theorem PuiseuxOriginal.rawVarietyComparison_apply (x : RESDimensionFreeRing.Ring originalPuiseuxGround) :
    rawVarietyComparison x = DiagonalConstructible.toVarietyRing (rawRESComparison x) := rfl

end DiamondIntegral.Section5
