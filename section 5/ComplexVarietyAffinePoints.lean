import «section 5».ComplexVarietyCharts
import «section 5».AffineCoordinateAlgebras
import «section 5».AffinePointFiniteEquations

/-! Actual K-valued scheme points over C are identified with algebra
points on every affine chart, before encoding them as VF tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
variable {K : Type} [Field K] [Algebra ℂ K]

def ComplexVariety.Point (X : ComplexVariety) :=
  {p : Spec (.of K) ⟶ X.scheme | p ≫ X.toC = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))}

@[instance_reducible] def ComplexVariety.coordinateAlgebra (X : ComplexVariety) [IsAffine X.scheme] : Algebra ℂ Γ(X.scheme, ⊤) :=
  (Spec.preimage (X.scheme.isoSpec.inv ≫ X.toC)).hom.toAlgebra

attribute [local instance] ComplexVariety.coordinateAlgebra

theorem ComplexVariety.coordinateSpec_toC (X : ComplexVariety) [IsAffine X.scheme] :
    Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) = X.scheme.isoSpec.inv ≫ X.toC :=
  Spec.map_preimage _

theorem ComplexVariety.coordinateIso_overC (X : ComplexVariety) [IsAffine X.scheme] :
    X.scheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.scheme, ⊤))) = X.toC := by
  rw [X.coordinateSpec_toC,← Category.assoc,X.scheme.isoSpec.hom_inv_id,Category.id_comp]

def ComplexVariety.affinePointEquiv (X : ComplexVariety) [IsAffine X.scheme] :
    X.Point (K := K) ≃ (Γ(X.scheme, ⊤) →ₐ[ℂ] K) where
  toFun p := specOverAlgHom (p.val ≫ X.scheme.isoSpec.hom) (by
    rw [Category.assoc,X.coordinateIso_overC]
    exact p.property)
  invFun f := ⟨Spec.map (CommRingCat.ofHom f.toRingHom) ≫ X.scheme.isoSpec.inv,by
    change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ X.scheme.isoSpec.inv) ≫ X.toC = _
    rw [Category.assoc,← X.coordinateSpec_toC]
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact f.commutes c⟩
  left_inv p := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom (specOverAlgHom _ _).toRingHom) ≫ X.scheme.isoSpec.inv = p.val
    rw [specOverAlgHom_map,Category.assoc,X.scheme.isoSpec.hom_inv_id,Category.comp_id]
  right_inv f := by
    apply specMapAlgHom_injective
    change Spec.map (CommRingCat.ofHom (specOverAlgHom _ _).toRingHom) = Spec.map (CommRingCat.ofHom f.toRingHom)
    exact (specOverAlgHom_map _ _).trans (by
      rw [Category.assoc,X.scheme.isoSpec.inv_hom_id]
      exact Category.comp_id _)

end DiamondIntegral.Section5
