import «section 5».AffineSpaceProducts
import «section 5».RationalAffineCoordinateMaps
import «section 5».VarietyMorphisms

/-! Two actual equivariant affine-coordinate maps give an actual map
to their product. An immersed coordinate makes the pair map an immersion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety
attribute [local instance] Object.reduced
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)

theorem rationalAffine_product_hom_ext {W : Scheme.{0}}
    (f g : W ⟶ (rationalAffineObject (Fin.append q r)).scheme)
    (hL : f ≫ (rationalAffineLeft q r).hom = g ≫ (rationalAffineLeft q r).hom)
    (hR : f ≫ (rationalAffineRight q r).hom = g ≫ (rationalAffineRight q r).hom) : f = g := by
  apply (cancel_mono (affineSpaceReducedProductIso n m).hom).mp
  apply reducedPullback_hom_ext (rationalAffineObject q).toC (rationalAffineObject r).toC
  · have he : (affineSpaceReducedProductIso n m).hom ≫
        reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC =
        (rationalAffineLeft q r).hom := affineSpaceReducedProductIso_fst n m
    rw [Category.assoc, Category.assoc, he]
    exact hL
  · have he : (affineSpaceReducedProductIso n m).hom ≫
        reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC =
        (rationalAffineRight q r).hom := affineSpaceReducedProductIso_snd n m
    rw [Category.assoc, Category.assoc, he]
    exact hR

variable {Y : EquivariantVariety.Object}
variable (f : Morphism Y (rationalAffineObject q)) (g : Morphism Y (rationalAffineObject r))

def rationalAffinePairMap : Y.scheme ⟶ (rationalAffineObject (Fin.append q r)).scheme :=
  reducedPullbackLift (rationalAffineObject q).toC (rationalAffineObject r).toC f.hom g.hom
    (f.overC.trans g.overC.symm) ≫ (affineSpaceReducedProductIso n m).inv

@[reassoc]
theorem rationalAffinePairMap_fst :
    rationalAffinePairMap q r f g ≫ (rationalAffineLeft q r).hom = f.hom := by
  let μ := reducedPullbackLift (rationalAffineObject q).toC (rationalAffineObject r).toC f.hom g.hom
    (f.overC.trans g.overC.symm)
  let e := affineSpaceReducedProductIso n m
  have he : e.hom ≫ reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC =
      (rationalAffineLeft q r).hom := affineSpaceReducedProductIso_fst n m
  calc
    (μ ≫ e.inv) ≫ (rationalAffineLeft q r).hom = μ ≫ (e.inv ≫ (rationalAffineLeft q r).hom) := Category.assoc _ _ _
    _ = μ ≫ reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC := by rw [← he]; simp
    _ = _ := reducedPullbackLift_fst _ _ _ _ _

@[reassoc]
theorem rationalAffinePairMap_snd :
    rationalAffinePairMap q r f g ≫ (rationalAffineRight q r).hom = g.hom := by
  let μ := reducedPullbackLift (rationalAffineObject q).toC (rationalAffineObject r).toC f.hom g.hom
    (f.overC.trans g.overC.symm)
  let e := affineSpaceReducedProductIso n m
  have he : e.hom ≫ reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC =
      (rationalAffineRight q r).hom := affineSpaceReducedProductIso_snd n m
  calc
    (μ ≫ e.inv) ≫ (rationalAffineRight q r).hom = μ ≫ (e.inv ≫ (rationalAffineRight q r).hom) := Category.assoc _ _ _
    _ = μ ≫ reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC := by rw [← he]; simp
    _ = _ := reducedPullbackLift_snd _ _ _ _ _

def rationalAffinePair : Morphism Y (rationalAffineObject (Fin.append q r)) where
  hom := rationalAffinePairMap q r f g
  overC := by rw [← (rationalAffineLeft q r).overC, ← Category.assoc, rationalAffinePairMap_fst, f.overC]
  equivariant η := by
    apply rationalAffine_product_hom_ext q r
    · calc
        _ = (Y.action η).asIso.hom ≫ f.hom := by rw [Category.assoc, rationalAffinePairMap_fst]
        _ = f.hom ≫ ((rationalAffineObject q).action η).asIso.hom := f.equivariant η
        _ = (rationalAffinePairMap q r f g ≫ (rationalAffineLeft q r).hom) ≫
            ((rationalAffineObject q).action η).asIso.hom := by rw [rationalAffinePairMap_fst]
        _ = rationalAffinePairMap q r f g ≫ ((rationalAffineLeft q r).hom ≫
            ((rationalAffineObject q).action η).asIso.hom) := Category.assoc _ _ _
        _ = rationalAffinePairMap q r f g ≫ (((rationalAffineObject (Fin.append q r)).action η).asIso.hom ≫
            (rationalAffineLeft q r).hom) := congrArg (fun h => rationalAffinePairMap q r f g ≫ h)
          ((rationalAffineLeft q r).equivariant η).symm
        _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = (Y.action η).asIso.hom ≫ g.hom := by rw [Category.assoc, rationalAffinePairMap_snd]
        _ = g.hom ≫ ((rationalAffineObject r).action η).asIso.hom := g.equivariant η
        _ = (rationalAffinePairMap q r f g ≫ (rationalAffineRight q r).hom) ≫
            ((rationalAffineObject r).action η).asIso.hom := by rw [rationalAffinePairMap_snd]
        _ = rationalAffinePairMap q r f g ≫ ((rationalAffineRight q r).hom ≫
            ((rationalAffineObject r).action η).asIso.hom) := Category.assoc _ _ _
        _ = rationalAffinePairMap q r f g ≫ (((rationalAffineObject (Fin.append q r)).action η).asIso.hom ≫
            (rationalAffineRight q r).hom) := congrArg (fun h => rationalAffinePairMap q r f g ≫ h)
          ((rationalAffineRight q r).equivariant η).symm
        _ = _ := (Category.assoc _ _ _).symm

theorem rationalAffinePair_immersion [IsImmersion f.hom] : IsImmersion (rationalAffinePair q r f g).hom := by
  haveI : IsImmersion ((rationalAffinePair q r f g).hom ≫ (rationalAffineLeft q r).hom) := by
    change IsImmersion (rationalAffinePairMap q r f g ≫ (rationalAffineLeft q r).hom)
    rw [rationalAffinePairMap_fst]
    infer_instance
  exact IsImmersion.of_comp _ (rationalAffineLeft q r).hom

end DiamondIntegral.Section5
