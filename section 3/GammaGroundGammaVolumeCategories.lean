import «section 3».GammaGroundGammaCategories
import «section 3».GammaGroundMeasuredRVCategories
import «section 3».GammaVolumeCategories

/-! Definition 3.16 and the Gamma part of Notation 3.17. Gamma is written
multiplicatively in Lean: sums of coordinates become finite products. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundGammaObject.coordinates (A : GammaGroundGammaObject hc ground k) (a : A.Carrier) :
    Fin k → Values.Gamma (M := M) := fun i => cast (gammaCarrier hc) (a.2.val i)

structure GammaGroundMeasuredGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  underlying : GammaGroundGammaObject hc ground k
  form : ∀ i, GammaGroundVolumeForm hc ground (underlying.piece i)

def GammaGroundMeasuredGammaObject.weight (A : GammaGroundMeasuredGammaObject hc ground k)
    (a : A.underlying.Carrier) : Values.Gamma (M := M) := gammaGroundFormValue (A.form a.1) a.2

def GammaGroundMeasuredGammaObject.combinedWeight (A : GammaGroundMeasuredGammaObject hc ground k)
    (a : A.underlying.Carrier) : Values.Gamma (M := M) :=
  A.weight a * ∏ i, A.underlying.coordinates a i

theorem gammaGroundMeasuredGamma_equation_iff (A B : GammaGroundMeasuredGammaObject hc ground k)
    (f : GammaGroundGammaHom A.underlying B.underlying) (a : A.underlying.Carrier) :
    A.weight a = B.weight (f.bijection.equiv a) *
      gammaTupleJacobian (A.underlying.coordinates a)
        (B.underlying.coordinates (f.bijection.equiv a)) ↔
    A.combinedWeight a = B.combinedWeight (f.bijection.equiv a) := by
  unfold gammaTupleJacobian GammaGroundMeasuredGammaObject.combinedWeight
  rw [← mul_div_assoc, eq_div_iff_mul_eq']

structure GammaGroundMeasuredGammaHom (A B : GammaGroundMeasuredGammaObject hc ground k) where
  underlying : GammaGroundGammaHom A.underlying B.underlying
  preserves : ∀ a, A.combinedWeight a = B.combinedWeight (underlying.bijection.equiv a)

namespace GammaGroundMeasuredGammaHom
variable {A B D : GammaGroundMeasuredGammaObject hc ground k}

@[ext] theorem ext {f g : GammaGroundMeasuredGammaHom A B} (h : f.underlying = g.underlying) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundMeasuredGammaHom A A :=
  ⟨GammaGroundGammaHom.id A.underlying, fun _ => rfl⟩

def comp (g : GammaGroundMeasuredGammaHom B D) (f : GammaGroundMeasuredGammaHom A B) : GammaGroundMeasuredGammaHom A D :=
  ⟨g.underlying.comp f.underlying,
    fun a => (f.preserves a).trans (g.preserves (f.underlying.bijection.equiv a))⟩

def symm (f : GammaGroundMeasuredGammaHom A B) : GammaGroundMeasuredGammaHom B A where
  underlying := f.underlying.symm
  preserves b := by
    have h := f.preserves (f.underlying.bijection.equiv.symm b)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

end GammaGroundMeasuredGammaHom

instance gammaGroundMeasuredGammaGroupoid : Groupoid (GammaGroundMeasuredGammaObject hc ground k) where
  Hom := GammaGroundMeasuredGammaHom
  id := GammaGroundMeasuredGammaHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundMeasuredGammaHom.ext; apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.refl_trans _
  comp_id f := by apply GammaGroundMeasuredGammaHom.ext; apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.trans_refl _
  assoc f g h := by apply GammaGroundMeasuredGammaHom.ext; apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.trans_assoc _ _ _
  inv_comp f := by apply GammaGroundMeasuredGammaHom.ext; apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.symm_trans_self _
  comp_inv f := by apply GammaGroundMeasuredGammaHom.ext; apply GammaGroundGammaHom.ext; apply GammaGroundFamilyBijection.ext; exact Equiv.self_trans_symm _

def gammaGroundMeasuredFiniteGammaProperty : ObjectProperty (GammaGroundMeasuredGammaObject hc ground k) :=
  fun A => gammaGroundFiniteGammaProperty A.underlying

abbrev GammaGroundMeasuredFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  (gammaGroundMeasuredFiniteGammaProperty (hc := hc) (ground := ground) (k := k)).FullSubcategory

end DiamondIntegral.Section3
