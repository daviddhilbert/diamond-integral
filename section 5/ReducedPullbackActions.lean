import «section 5».ReducedSchemeProducts
import Mathlib.CategoryTheory.Endomorphism

/-! Equivariant reduced fibre products carry the induced actual group
action. Both projections and finite-level inflation are checked. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
attribute [local instance] reducedPullback_isReduced
variable {X Y Z : Scheme} {G : Type} [Group G]
variable (f : X ⟶ Z) (g : Y ⟶ Z)
variable (ρX : G →* Aut X) (ρY : G →* Aut Y) (ρZ : G →* Aut Z)
variable (hf : ∀ h, (ρX h).asIso.hom ≫ f = f ≫ (ρZ h).asIso.hom)
variable (hg : ∀ h, (ρY h).asIso.hom ≫ g = g ≫ (ρZ h).asIso.hom)

def reducedPullbackActionMap (h : G) : reducedPullback f g ⟶ reducedPullback f g :=
  reducedPullbackLift f g (reducedPullbackFst f g ≫ (ρX h).asIso.hom)
    (reducedPullbackSnd f g ≫ (ρY h).asIso.hom) (by
      rw [Category.assoc, Category.assoc, hf, hg, ← Category.assoc, ← Category.assoc,
        reducedPullback_condition])

@[reassoc]
theorem reducedPullbackActionMap_fst (h : G) :
    reducedPullbackActionMap f g ρX ρY ρZ hf hg h ≫ reducedPullbackFst f g =
      reducedPullbackFst f g ≫ (ρX h).asIso.hom := reducedPullbackLift_fst _ _ _ _ _

@[reassoc]
theorem reducedPullbackActionMap_snd (h : G) :
    reducedPullbackActionMap f g ρX ρY ρZ hf hg h ≫ reducedPullbackSnd f g =
      reducedPullbackSnd f g ≫ (ρY h).asIso.hom := reducedPullbackLift_snd _ _ _ _ _

theorem reducedPullbackActionMap_one :
    reducedPullbackActionMap f g ρX ρY ρZ hf hg 1 = 𝟙 _ := by
  apply reducedPullback_hom_ext f g
  · rw [reducedPullbackActionMap_fst, map_one]
    simp
  · rw [reducedPullbackActionMap_snd, map_one]
    simp

theorem reducedPullbackActionMap_mul (h k : G) :
    reducedPullbackActionMap f g ρX ρY ρZ hf hg k ≫
      reducedPullbackActionMap f g ρX ρY ρZ hf hg h =
        reducedPullbackActionMap f g ρX ρY ρZ hf hg (h * k) := by
  apply reducedPullback_hom_ext f g
  · simp only [Category.assoc, reducedPullbackActionMap_fst,
      reducedPullbackActionMap_fst_assoc, map_mul]
    rfl
  · simp only [Category.assoc, reducedPullbackActionMap_snd,
      reducedPullbackActionMap_snd_assoc, map_mul]
    rfl

def reducedPullbackSchemeAction : G →* Aut (reducedPullback f g) where
  toFun h := .of {
    hom := reducedPullbackActionMap f g ρX ρY ρZ hf hg h
    inv := reducedPullbackActionMap f g ρX ρY ρZ hf hg h⁻¹
    hom_inv_id := by rw [reducedPullbackActionMap_mul, inv_mul_cancel, reducedPullbackActionMap_one]
    inv_hom_id := by rw [reducedPullbackActionMap_mul, mul_inv_cancel, reducedPullbackActionMap_one] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact reducedPullbackActionMap_one f g ρX ρY ρZ hf hg
  map_mul' h k := by
    apply Aut.ext
    apply Iso.ext
    exact (reducedPullbackActionMap_mul f g ρX ρY ρZ hf hg h k).symm

theorem reducedPullbackSchemeAction_fst (h : G) :
    (reducedPullbackSchemeAction f g ρX ρY ρZ hf hg h).asIso.hom ≫ reducedPullbackFst f g =
      reducedPullbackFst f g ≫ (ρX h).asIso.hom := reducedPullbackActionMap_fst f g ρX ρY ρZ hf hg h

theorem reducedPullbackSchemeAction_snd (h : G) :
    (reducedPullbackSchemeAction f g ρX ρY ρZ hf hg h).asIso.hom ≫ reducedPullbackSnd f g =
      reducedPullbackSnd f g ≫ (ρY h).asIso.hom := reducedPullbackActionMap_snd f g ρX ρY ρZ hf hg h

theorem reducedPullbackSchemeAction_comp {H : Type} [Group H] (π : H →* G) :
    reducedPullbackSchemeAction f g (ρX.comp π) (ρY.comp π) (ρZ.comp π)
      (fun h => hf (π h)) (fun h => hg (π h)) =
        (reducedPullbackSchemeAction f g ρX ρY ρZ hf hg).comp π := by
  apply MonoidHom.ext
  intro h
  apply Aut.ext
  apply Iso.ext
  apply reducedPullback_hom_ext f g
  · exact (reducedPullbackSchemeAction_fst f g (ρX.comp π) (ρY.comp π) (ρZ.comp π)
      (fun h => hf (π h)) (fun h => hg (π h)) h).trans
        (reducedPullbackSchemeAction_fst f g ρX ρY ρZ hf hg (π h)).symm
  · exact (reducedPullbackSchemeAction_snd f g (ρX.comp π) (ρY.comp π) (ρZ.comp π)
      (fun h => hf (π h)) (fun h => hg (π h)) h).trans
        (reducedPullbackSchemeAction_snd f g ρX ρY ρZ hf hg (π h)).symm

end DiamondIntegral.Section5
