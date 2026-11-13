import «section 3».GammaGroundCodePresentations
import «section 3».GammaCategories
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
abbrev GammaGroundGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  GammaGroundFiniteFamily hc ground ((volumeGammaSpace hc).power (Fin k))

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

/-- These are RV codes, not arbitrary real representatives of an imaginary. -/
theorem gammaGroundGammaTupleSpace_rvCoded : ((volumeGammaSpace hc).power (Fin k)).RVCoded := by
  have h : (volumeGammaSpace hc).RVCoded := by
    intro c i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact c.property.1
  exact h.power _ (Fin k)

structure GammaGroundGammaHom (A B : GammaGroundGammaObject hc ground k) where
  bijection : GammaGroundFamilyBijection A B
  contraction : ∃ f : GammaGroundFamilyBijection A.codeLift B.codeLift,
    ∀ c, B.decode (f.equiv c) = bijection.equiv (A.decode c)

namespace GammaGroundGammaHom
variable {A B D : GammaGroundGammaObject hc ground k}

@[ext] theorem ext {f g : GammaGroundGammaHom A B} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : GammaGroundGammaObject hc ground k) : GammaGroundGammaHom A A :=
  ⟨GammaGroundFamilyBijection.id A, GammaGroundFamilyBijection.id A.codeLift, fun _ => rfl⟩

def comp (g : GammaGroundGammaHom B D) (f : GammaGroundGammaHom A B) : GammaGroundGammaHom A D where
  bijection := g.bijection.comp f.bijection
  contraction := by
    obtain ⟨F, hF⟩ := f.contraction
    obtain ⟨G, hG⟩ := g.contraction
    exact ⟨G.comp F, fun c => (hG (F.equiv c)).trans (congrArg g.bijection.equiv (hF c))⟩

def symm (f : GammaGroundGammaHom A B) : GammaGroundGammaHom B A where
  bijection := f.bijection.symm
  contraction := by
    obtain ⟨F, hF⟩ := f.contraction
    refine ⟨F.symm, fun c => ?_⟩
    have h := hF (F.equiv.symm c)
    rw [Equiv.apply_symm_apply] at h
    exact f.bijection.equiv.eq_symm_apply.mpr h.symm

end GammaGroundGammaHom

instance gammaGroundGammaObjectGroupoid : Groupoid (GammaGroundGammaObject hc ground k) where
  Hom := GammaGroundGammaHom
  id := GammaGroundGammaHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.refl_trans _
  comp_id f := by apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.trans_refl _
  assoc f g h := by apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.trans_assoc _ _ _
  inv_comp f := by apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.symm_trans_self _
  comp_inv f := by apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.self_trans_symm _

def gammaGroundFiniteGammaProperty : ObjectProperty (GammaGroundGammaObject hc ground k) :=
  fun A => ∀ i, (A.piece i).carrier.Finite

abbrev GammaGroundFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  (gammaGroundFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).FullSubcategory

end DiamondIntegral.Section3
