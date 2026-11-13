import «section 4».FieldScissorBijection

/-! The scissor equality follows from an explicit pure-field definable
bijection in the positive-expression presentation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.FieldScissorClasses
open FieldDefinableRing
variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem objectClass_scissor {n : ℕ} (A B C D : Set (Fin n → K))
    (hA : PureDef A) (hB : PureDef B) (hC : PureDef C) (hD : PureDef D)
    (hc : C = A ∪ B) (hd : D = A ∩ B) :
    objectClass K ⟨n, C, hC⟩ + objectClass K ⟨n, D, hD⟩ =
      objectClass K ⟨n, A, hA⟩ + objectClass K ⟨n, B, hB⟩ := by
  subst C
  subst D
  let a : Chart K := ⟨n, A, hA⟩
  let b : Chart K := ⟨n, B, hB⟩
  let c : Chart K := ⟨n, A ∪ B, hC⟩
  let d : Chart K := ⟨n, A ∩ B, hD⟩
  have h := relation_zero K (.add (.atom c) (.atom d)) (.add (.atom a) (.atom b))
    (FieldScissorBijection.graph A) (FieldScissorBijection.graph_definable A hA)
    (FieldScissorBijection.biunique A B)
  change Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of c + FreeCommRing.of d) =
    Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a + FreeCommRing.of b) at h
  change Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of c) +
      Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of d) =
    Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of a) +
      Ideal.Quotient.mk (relationIdeal K) (FreeCommRing.of b)
  simpa only [map_add] using h

end DiamondIntegral.Section4.FieldScissorClasses
