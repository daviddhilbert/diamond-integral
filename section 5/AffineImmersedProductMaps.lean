import «section 5».AffineSpaceProducts
import «section 5».ReducedPullbackMaps
import «section 5».RationalAffineCoordinateMaps
import «section 5».VarietyImmersedObjects
import «section 5».VarietyImmersionPartitions

/-! Products of actual reduced immersed varieties have actual immersions
into the rational diagonal product affine space. The image formula is
proved on all scheme points, before using it to construct the good action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety
attribute [local instance] reducedPullback_isReduced reducedPullbackMap_immersion
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
variable {Y Z : EquivariantVariety.Object}
variable (f : Morphism Y (rationalAffineObject q)) (g : Morphism Z (rationalAffineObject r))

def affineImmersedProductMap : reducedPullback Y.toC Z.toC ⟶ (rationalAffineObject (Fin.append q r)).scheme :=
  reducedPullbackMap Y.toC Z.toC (rationalAffineObject q).toC (rationalAffineObject r).toC
    f.hom g.hom f.overC.symm g.overC.symm ≫ (affineSpaceReducedProductIso n m).inv

@[reassoc]
theorem affineImmersedProductMap_fst :
    affineImmersedProductMap q r f g ≫ (rationalAffineLeft q r).hom = reducedPullbackFst Y.toC Z.toC ≫ f.hom := by
  let μ := reducedPullbackMap Y.toC Z.toC (rationalAffineObject q).toC (rationalAffineObject r).toC
    f.hom g.hom f.overC.symm g.overC.symm
  let e := affineSpaceReducedProductIso n m
  have he : e.hom ≫ reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC =
      (rationalAffineLeft q r).hom := affineSpaceReducedProductIso_fst n m
  calc
    (μ ≫ e.inv) ≫ (rationalAffineLeft q r).hom = μ ≫ (e.inv ≫ (rationalAffineLeft q r).hom) := Category.assoc _ _ _
    _ = μ ≫ reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC := by
      rw [← he]
      simp
    _ = _ := reducedPullbackMap_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem affineImmersedProductMap_snd :
    affineImmersedProductMap q r f g ≫ (rationalAffineRight q r).hom = reducedPullbackSnd Y.toC Z.toC ≫ g.hom := by
  let μ := reducedPullbackMap Y.toC Z.toC (rationalAffineObject q).toC (rationalAffineObject r).toC
    f.hom g.hom f.overC.symm g.overC.symm
  let e := affineSpaceReducedProductIso n m
  have he : e.hom ≫ reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC =
      (rationalAffineRight q r).hom := affineSpaceReducedProductIso_snd n m
  calc
    (μ ≫ e.inv) ≫ (rationalAffineRight q r).hom = μ ≫ (e.inv ≫ (rationalAffineRight q r).hom) := Category.assoc _ _ _
    _ = μ ≫ reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC := by
      rw [← he]
      simp
    _ = _ := reducedPullbackMap_snd _ _ _ _ _ _ _ _

theorem affineImmersedProductMap_immersion [IsImmersion f.hom] [IsImmersion g.hom] :
    IsImmersion (affineImmersedProductMap q r f g) := by
  unfold affineImmersedProductMap
  infer_instance

theorem affineImmersedProductMap_range :
    Set.range (affineImmersedProductMap q r f g) =
      (rationalAffineLeft q r).hom ⁻¹' Set.range f.hom ∩ (rationalAffineRight q r).hom ⁻¹' Set.range g.hom := by
  let μ := reducedPullbackMap Y.toC Z.toC (rationalAffineObject q).toC (rationalAffineObject r).toC
    f.hom g.hom f.overC.symm g.overC.symm
  let e := affineSpaceReducedProductIso n m
  have he : Set.range (affineImmersedProductMap q r f g) = e.hom ⁻¹' Set.range μ := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨p, ?_⟩
      exact ((Scheme.homeoOfIso e).apply_symm_apply (μ p)).symm
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      exact (congrArg e.inv hp).trans ((Scheme.homeoOfIso e).symm_apply_apply z)
  rw [he, reducedPullbackMap_range]
  ext z
  have hL := congrArg (fun h => h z) (affineSpaceReducedProductIso_fst n m)
  have hR := congrArg (fun h => h z) (affineSpaceReducedProductIso_snd n m)
  change reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC (e.hom z) =
    (rationalAffineLeft q r).hom z at hL
  change reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC (e.hom z) =
    (rationalAffineRight q r).hom z at hR
  change (reducedPullbackFst (rationalAffineObject q).toC (rationalAffineObject r).toC (e.hom z) ∈ Set.range f.hom ∧
    reducedPullbackSnd (rationalAffineObject q).toC (rationalAffineObject r).toC (e.hom z) ∈ Set.range g.hom) ↔ _
  exact and_congr (Iff.of_eq (congrArg (fun p => p ∈ Set.range f.hom) hL))
    (Iff.of_eq (congrArg (fun p => p ∈ Set.range g.hom) hR))

theorem affineImmersedProductMap_invariant :
    (rationalAffineObject (Fin.append q r)).Invariant (Set.range (affineImmersedProductMap q r f g)) := by
  intro η z
  simp only [affineImmersedProductMap_range, Set.mem_inter_iff, Set.mem_preimage]
  have hL := congrArg (fun h => h z) ((rationalAffineLeft q r).equivariant η)
  have hR := congrArg (fun h => h z) ((rationalAffineRight q r).equivariant η)
  change (rationalAffineLeft q r).hom (schemePointAction (rationalAffineObject (Fin.append q r)).action η z) =
    schemePointAction (rationalAffineObject q).action η ((rationalAffineLeft q r).hom z) at hL
  change (rationalAffineRight q r).hom (schemePointAction (rationalAffineObject (Fin.append q r)).action η z) =
    schemePointAction (rationalAffineObject r).action η ((rationalAffineRight q r).hom z) at hR
  rw [hL, hR]
  exact and_congr (f.range_invariant η _) (g.range_invariant η _)

attribute [local instance] affineImmersedProductMap_immersion

def affineImmersedProductObject [IsImmersion f.hom] [IsImmersion g.hom] : EquivariantVariety.Object :=
  invariantImmersedObject (rationalAffineObject (Fin.append q r)) (affineImmersedProductMap q r f g)
    (affineImmersedProductMap_invariant q r f g)

def affineImmersedProductInclusion [IsImmersion f.hom] [IsImmersion g.hom] :
    Morphism (affineImmersedProductObject q r f g) (rationalAffineObject (Fin.append q r)) :=
  invariantImmersedInclusion (rationalAffineObject (Fin.append q r)) (affineImmersedProductMap q r f g)
    (affineImmersedProductMap_invariant q r f g)

@[instance]
theorem affineImmersedProductInclusion_immersion [IsImmersion f.hom] [IsImmersion g.hom] :
    IsImmersion (affineImmersedProductInclusion q r f g).hom :=
  affineImmersedProductMap_immersion q r f g

end DiamondIntegral.Section5
