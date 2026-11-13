import «section 4».FieldAffineNontrivial

/-! The natural quotient from the pure-field definable ring to its
affine-line quotient, constructed from inclusion of the defining ideals. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FieldAffineQuotientMap
open FieldDefinableRing
variable (K : Type) [Field K] [FirstOrder.Ring.CompatibleRing K]

theorem ideal_le : relationIdeal K ≤ Ideal.span (affineRelations K) :=
  Ideal.span_mono (fun _ hr => Set.mem_insert_of_mem _ hr)

def quotient : FieldDefinableRing.Ring K →+* AffineQuotient K :=
  Ideal.Quotient.lift (relationIdeal K) (Ideal.Quotient.mk (Ideal.span (affineRelations K)))
    (fun _ hr => Ideal.Quotient.eq_zero_iff_mem.mpr (ideal_le K hr))

theorem quotient_objectClass (a : Chart K) : quotient K (objectClass K a) =
    Ideal.Quotient.mk (Ideal.span (affineRelations K)) (FreeCommRing.of a) := rfl

theorem quotient_affine : quotient K (affineClass K) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))

end DiamondIntegral.Section4.FieldAffineQuotientMap
