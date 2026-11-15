import «section 5».VarietyMorphisms
import «section 5».ReducedPullbackMaps

/-! Actual equivariant maps between geometric reduced product
presentations, including their immersion properties and complete point images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] reducedPullbackMap_immersion
variable {P X Y Q X' Y' : Object}

def ProductPresentation.fst (c : ProductPresentation P X Y) : Morphism P X where
  hom := c.iso.hom ≫ reducedPullbackFst X.toC Y.toC
  overC := c.overC
  equivariant := c.fst_equivariant

def ProductPresentation.snd (c : ProductPresentation P X Y) : Morphism P Y where
  hom := c.iso.hom ≫ reducedPullbackSnd X.toC Y.toC
  overC := by
    calc
      (c.iso.hom ≫ reducedPullbackSnd X.toC Y.toC) ≫ Y.toC =
          c.iso.hom ≫ (reducedPullbackSnd X.toC Y.toC ≫ Y.toC) := Category.assoc _ _ _
      _ = c.iso.hom ≫ (reducedPullbackFst X.toC Y.toC ≫ X.toC) :=
        congrArg (fun m => c.iso.hom ≫ m) (reducedPullback_condition X.toC Y.toC).symm
      _ = _ := c.overC
  equivariant := c.snd_equivariant

theorem ProductPresentation.hom_ext (c : ProductPresentation P X Y) {W : Scheme.{0}}
    (a b : W ⟶ P.scheme) (hL : a ≫ c.fst.hom = b ≫ c.fst.hom)
    (hR : a ≫ c.snd.hom = b ≫ c.snd.hom) : a = b := by
  apply (cancel_mono c.iso.hom).mp
  apply reducedPullback_hom_ext X.toC Y.toC
  · simpa only [ProductPresentation.fst, Category.assoc] using hL
  · simpa only [ProductPresentation.snd, Category.assoc] using hR

def ProductPresentation.morphismOfProjections (c : ProductPresentation P X Y)
    (M : Q.scheme ⟶ P.scheme) (a : Morphism Q X) (b : Morphism Q Y)
    (hL : M ≫ c.fst.hom = a.hom) (hR : M ≫ c.snd.hom = b.hom) : Morphism Q P where
  hom := M
  overC := by rw [← c.fst.overC, ← Category.assoc, hL, a.overC]
  equivariant h := by
    apply c.hom_ext
    · calc
        _ = (Q.action h).asIso.hom ≫ a.hom := by rw [Category.assoc, hL]
        _ = a.hom ≫ (X.action h).asIso.hom := a.equivariant h
        _ = (M ≫ c.fst.hom) ≫ (X.action h).asIso.hom := by rw [hL]
        _ = M ≫ (c.fst.hom ≫ (X.action h).asIso.hom) := Category.assoc _ _ _
        _ = M ≫ ((P.action h).asIso.hom ≫ c.fst.hom) :=
          congrArg (fun m => M ≫ m) (c.fst.equivariant h).symm
        _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = (Q.action h).asIso.hom ≫ b.hom := by rw [Category.assoc, hR]
        _ = b.hom ≫ (Y.action h).asIso.hom := b.equivariant h
        _ = (M ≫ c.snd.hom) ≫ (Y.action h).asIso.hom := by rw [hR]
        _ = M ≫ (c.snd.hom ≫ (Y.action h).asIso.hom) := Category.assoc _ _ _
        _ = M ≫ ((P.action h).asIso.hom ≫ c.snd.hom) :=
          congrArg (fun m => M ≫ m) (c.snd.equivariant h).symm
        _ = _ := (Category.assoc _ _ _).symm

def ProductPresentation.mapHom (c : ProductPresentation P X Y) (d : ProductPresentation Q X' Y')
    (f : Morphism X' X) (g : Morphism Y' Y) : Q.scheme ⟶ P.scheme :=
  d.iso.hom ≫ reducedPullbackMap X'.toC Y'.toC X.toC Y.toC f.hom g.hom f.overC.symm g.overC.symm ≫ c.iso.inv

@[reassoc]
theorem ProductPresentation.mapHom_fst (c : ProductPresentation P X Y) (d : ProductPresentation Q X' Y')
    (f : Morphism X' X) (g : Morphism Y' Y) : c.mapHom d f g ≫ c.fst.hom = d.fst.hom ≫ f.hom := by
  dsimp only [ProductPresentation.mapHom, ProductPresentation.fst]
  simp only [Category.assoc, c.iso.inv_hom_id_assoc, reducedPullbackMap_fst]

@[reassoc]
theorem ProductPresentation.mapHom_snd (c : ProductPresentation P X Y) (d : ProductPresentation Q X' Y')
    (f : Morphism X' X) (g : Morphism Y' Y) : c.mapHom d f g ≫ c.snd.hom = d.snd.hom ≫ g.hom := by
  dsimp only [ProductPresentation.mapHom, ProductPresentation.snd]
  simp only [Category.assoc, c.iso.inv_hom_id_assoc, reducedPullbackMap_snd]

def ProductPresentation.map (c : ProductPresentation P X Y) (d : ProductPresentation Q X' Y')
    (f : Morphism X' X) (g : Morphism Y' Y) : Morphism Q P :=
  c.morphismOfProjections (c.mapHom d f g) (f.comp d.fst) (g.comp d.snd)
    (c.mapHom_fst d f g) (c.mapHom_snd d f g)

@[instance]
theorem ProductPresentation.map_immersion (c : ProductPresentation P X Y) (d : ProductPresentation Q X' Y')
    (f : Morphism X' X) (g : Morphism Y' Y) [IsImmersion f.hom] [IsImmersion g.hom] :
    IsImmersion (c.map d f g).hom := by
  change IsImmersion (c.mapHom d f g)
  unfold ProductPresentation.mapHom
  infer_instance

theorem ProductPresentation.map_range (c : ProductPresentation P X Y) (d : ProductPresentation Q X' Y')
    (f : Morphism X' X) (g : Morphism Y' Y) :
    Set.range (c.map d f g).hom = c.fst.hom ⁻¹' Set.range f.hom ∩ c.snd.hom ⁻¹' Set.range g.hom := by
  let μ := reducedPullbackMap X'.toC Y'.toC X.toC Y.toC f.hom g.hom f.overC.symm g.overC.symm
  have he : Set.range (c.map d f g).hom = c.iso.hom ⁻¹' Set.range μ := by
    ext p
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨d.iso.hom q, ?_⟩
      have hh := congrArg c.iso.hom hq
      exact ((Scheme.homeoOfIso c.iso).apply_symm_apply (μ (d.iso.hom q))).symm.trans hh
    · rintro ⟨q, hq⟩
      refine ⟨d.iso.inv q, ?_⟩
      change c.iso.inv (μ (d.iso.hom (d.iso.inv q))) = p
      exact (congrArg (fun x => c.iso.inv (μ x)) ((Scheme.homeoOfIso d.iso).apply_symm_apply q)).trans
        ((congrArg c.iso.inv hq).trans ((Scheme.homeoOfIso c.iso).symm_apply_apply p))
  rw [he, reducedPullbackMap_range]
  rfl

end DiamondIntegral.Section5.EquivariantVariety
