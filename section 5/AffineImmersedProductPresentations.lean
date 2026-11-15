import «section 5».AffineImmersedProductMaps
import «section 5».VarietyImmersionFactorizations

/-! The immersed reduced products are genuine equivariant products over
the complex base. Their geometric classes therefore multiply by a defining
product relation of the variety ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety
attribute [local instance] affineImmersedProductMap_immersion
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
variable {Y Z : EquivariantVariety.Object}
variable (f : Morphism Y (rationalAffineObject q)) (g : Morphism Z (rationalAffineObject r))
variable [IsImmersion f.hom] [IsImmersion g.hom]

def affineImmersedProductLeft : Morphism (affineImmersedProductObject q r f g) Y :=
  f.factorThrough ((rationalAffineLeft q r).comp (affineImmersedProductInclusion q r f g)) (by
    rintro _ ⟨p, rfl⟩
    refine ⟨reducedPullbackFst Y.toC Z.toC p, ?_⟩
    exact (congrArg (fun h => h p) (affineImmersedProductMap_fst q r f g)).symm)

def affineImmersedProductRight : Morphism (affineImmersedProductObject q r f g) Z :=
  g.factorThrough ((rationalAffineRight q r).comp (affineImmersedProductInclusion q r f g)) (by
    rintro _ ⟨p, rfl⟩
    refine ⟨reducedPullbackSnd Y.toC Z.toC p, ?_⟩
    exact (congrArg (fun h => h p) (affineImmersedProductMap_snd q r f g)).symm)

theorem affineImmersedProductLeft_hom :
    (affineImmersedProductLeft q r f g).hom = reducedPullbackFst Y.toC Z.toC := by
  apply (cancel_mono f.hom).mp
  unfold affineImmersedProductLeft
  rw [Morphism.factorThrough_fac]
  exact affineImmersedProductMap_fst q r f g

theorem affineImmersedProductRight_hom :
    (affineImmersedProductRight q r f g).hom = reducedPullbackSnd Y.toC Z.toC := by
  apply (cancel_mono g.hom).mp
  unfold affineImmersedProductRight
  rw [Morphism.factorThrough_fac]
  exact affineImmersedProductMap_snd q r f g

def affineImmersedProductPresentation : ProductPresentation (affineImmersedProductObject q r f g) Y Z where
  iso := CategoryTheory.Iso.refl _
  overC := by
    change reducedPullbackFst Y.toC Z.toC ≫ Y.toC = (affineImmersedProductObject q r f g).toC
    rw [← affineImmersedProductLeft_hom q r f g]
    exact (affineImmersedProductLeft q r f g).overC
  fst_equivariant η := by
    change ((affineImmersedProductObject q r f g).action η).asIso.hom ≫ reducedPullbackFst Y.toC Z.toC =
      reducedPullbackFst Y.toC Z.toC ≫ (Y.action η).asIso.hom
    rw [← affineImmersedProductLeft_hom q r f g]
    exact (affineImmersedProductLeft q r f g).equivariant η
  snd_equivariant η := by
    change ((affineImmersedProductObject q r f g).action η).asIso.hom ≫ reducedPullbackSnd Y.toC Z.toC =
      reducedPullbackSnd Y.toC Z.toC ≫ (Z.action η).asIso.hom
    rw [← affineImmersedProductRight_hom q r f g]
    exact (affineImmersedProductRight q r f g).equivariant η

theorem affineImmersedProductObject_class :
    objectClass (affineImmersedProductObject q r f g) = objectClass Y * objectClass Z :=
  objectClass_product _ _ _ (affineImmersedProductPresentation q r f g)

end DiamondIntegral.Section5
