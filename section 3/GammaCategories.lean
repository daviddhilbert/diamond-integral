import «section 3».CodePresentations
import «section 3».GammaVolumeForms
import Section4.VFAlgebraicCoordinates
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Definition 3.13. A Gamma object is a finite tagged family of genuine
definable subsets of Gamma powers. Arrows must have an actual definable
bijection on the full nonzero RV code families contracting to them. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev GammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  FiniteFamily ((volumeGammaSpace hc).power (Fin k)) S

variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

/-- These are RV codes, not arbitrary real representatives of an imaginary. -/
theorem gammaTupleSpace_rvCoded : ((volumeGammaSpace hc).power (Fin k)).RVCoded := by
  have h : (volumeGammaSpace hc).RVCoded := by
    intro c i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact c.property.1
  exact h.power _ (Fin k)

structure GammaHom (A B : GammaObject hc S k) where
  bijection : FamilyBijection A B
  contraction : ∃ f : FamilyBijection A.codeLift B.codeLift,
    ∀ c, B.decode (f.equiv c) = bijection.equiv (A.decode c)

namespace GammaHom
variable {A B D : GammaObject hc S k}

@[ext] theorem ext {f g : GammaHom A B} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : GammaObject hc S k) : GammaHom A A :=
  ⟨FamilyBijection.id A, FamilyBijection.id A.codeLift, fun _ => rfl⟩

def comp (g : GammaHom B D) (f : GammaHom A B) : GammaHom A D where
  bijection := g.bijection.comp f.bijection
  contraction := by
    obtain ⟨F, hF⟩ := f.contraction
    obtain ⟨G, hG⟩ := g.contraction
    exact ⟨G.comp F, fun c => (hG (F.equiv c)).trans (congrArg g.bijection.equiv (hF c))⟩

def symm (f : GammaHom A B) : GammaHom B A where
  bijection := f.bijection.symm
  contraction := by
    obtain ⟨F, hF⟩ := f.contraction
    refine ⟨F.symm, fun c => ?_⟩
    have h := hF (F.equiv.symm c)
    rw [Equiv.apply_symm_apply] at h
    exact f.bijection.equiv.eq_symm_apply.mpr h.symm

end GammaHom

instance gammaObjectGroupoid : Groupoid (GammaObject hc S k) where
  Hom := GammaHom
  id := GammaHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.refl_trans _
  comp_id f := by apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.trans_refl _
  assoc f g h := by apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.trans_assoc _ _ _
  inv_comp f := by apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.symm_trans_self _
  comp_inv f := by apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.self_trans_symm _

def finiteGammaProperty : ObjectProperty (GammaObject hc S k) :=
  fun A => ∀ i, (A.piece i).carrier.Finite

abbrev FiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  (finiteGammaProperty (hc := hc) (S := S) (k := k)).FullSubcategory

end DiamondIntegral.Section3
