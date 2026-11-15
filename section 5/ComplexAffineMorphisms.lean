import «section 5».ComplexVarietyAffinePoints

/-! Actual affine scheme morphisms over C act on all extension-field
points by their actual contravariant coordinate-algebra map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] ComplexVariety.coordinateAlgebra
variable {K : Type} [Field K] [Algebra ℂ K]
variable {X Y : ComplexVariety}

def ComplexVariety.Morphism.pointMap (f : X.Morphism Y) (p : X.Point (K := K)) : Y.Point (K := K) :=
  ⟨p.val ≫ f.hom,by
    change (p.val ≫ f.hom) ≫ Y.toC = _
    rw [Category.assoc,f.overC]
    exact p.property⟩

def ComplexVariety.Morphism.affineAlgebraMap [IsAffine X.scheme] [IsAffine Y.scheme]
    (f : X.Morphism Y) : Γ(Y.scheme, ⊤) →ₐ[ℂ] Γ(X.scheme, ⊤) :=
  specOverAlgHom (X.scheme.isoSpec.inv ≫ f.hom ≫ Y.scheme.isoSpec.hom) (by
    rw [Category.assoc,Category.assoc,Y.coordinateIso_overC,f.overC,← X.coordinateSpec_toC])

theorem ComplexVariety.Morphism.affineAlgebraMap_spec [IsAffine X.scheme] [IsAffine Y.scheme]
    (f : X.Morphism Y) :
    Spec.map (CommRingCat.ofHom f.affineAlgebraMap.toRingHom) =
      X.scheme.isoSpec.inv ≫ f.hom ≫ Y.scheme.isoSpec.hom := specOverAlgHom_map _ _

theorem ComplexVariety.Morphism.affinePointEquiv_map [IsAffine X.scheme] [IsAffine Y.scheme]
    (f : X.Morphism Y) (p : X.Point (K := K)) :
    Y.affinePointEquiv (f.pointMap p) = (X.affinePointEquiv p).comp f.affineAlgebraMap := by
  apply specMapAlgHom_injective
  change Spec.map (CommRingCat.ofHom (specOverAlgHom _ _).toRingHom) =
    Spec.map (CommRingCat.ofHom ((specOverAlgHom _ _).comp f.affineAlgebraMap).toRingHom)
  rw [specOverAlgHom_map,specMapAlgHom_comp,specOverAlgHom_map,f.affineAlgebraMap_spec]
  rw [Category.assoc,← Category.assoc X.scheme.isoSpec.hom X.scheme.isoSpec.inv,
    X.scheme.isoSpec.hom_inv_id,Category.id_comp]
  rfl

end DiamondIntegral.Section5
