import «section 3».GammaCategories

/-! Definition 3.16 and the Gamma part of Notation 3.17. Gamma is written
multiplicatively in Lean: sums of coordinates become finite products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def GammaObject.coordinates (A : GammaObject hc S k) (a : A.Carrier) :
    Fin k → Values.Gamma (M := M) := fun i => cast (gammaCarrier hc) (a.2.val i)

def gammaTupleJacobian (a b : Fin k → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  (∏ i, b i) / ∏ i, a i

structure MeasuredGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) where
  underlying : GammaObject hc S k
  form : ∀ i, GammaVolumeForm hc (underlying.piece i)

def MeasuredGammaObject.weight (A : MeasuredGammaObject hc S k)
    (a : A.underlying.Carrier) : Values.Gamma (M := M) := gammaFormValue (A.form a.1) a.2

def MeasuredGammaObject.combinedWeight (A : MeasuredGammaObject hc S k)
    (a : A.underlying.Carrier) : Values.Gamma (M := M) :=
  A.weight a * ∏ i, A.underlying.coordinates a i

theorem measuredGamma_equation_iff (A B : MeasuredGammaObject hc S k)
    (f : GammaHom A.underlying B.underlying) (a : A.underlying.Carrier) :
    A.weight a = B.weight (f.bijection.equiv a) *
      gammaTupleJacobian (A.underlying.coordinates a)
        (B.underlying.coordinates (f.bijection.equiv a)) ↔
    A.combinedWeight a = B.combinedWeight (f.bijection.equiv a) := by
  unfold gammaTupleJacobian MeasuredGammaObject.combinedWeight
  rw [← mul_div_assoc, eq_div_iff_mul_eq']

structure MeasuredGammaHom (A B : MeasuredGammaObject hc S k) where
  underlying : GammaHom A.underlying B.underlying
  preserves : ∀ a, A.combinedWeight a = B.combinedWeight (underlying.bijection.equiv a)

namespace MeasuredGammaHom
variable {A B D : MeasuredGammaObject hc S k}

@[ext] theorem ext {f g : MeasuredGammaHom A B} (h : f.underlying = g.underlying) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : MeasuredGammaObject hc S k) : MeasuredGammaHom A A :=
  ⟨GammaHom.id A.underlying, fun _ => rfl⟩

def comp (g : MeasuredGammaHom B D) (f : MeasuredGammaHom A B) : MeasuredGammaHom A D :=
  ⟨g.underlying.comp f.underlying,
    fun a => (f.preserves a).trans (g.preserves (f.underlying.bijection.equiv a))⟩

def symm (f : MeasuredGammaHom A B) : MeasuredGammaHom B A where
  underlying := f.underlying.symm
  preserves b := by
    have h := f.preserves (f.underlying.bijection.equiv.symm b)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

end MeasuredGammaHom

instance measuredGammaGroupoid : Groupoid (MeasuredGammaObject hc S k) where
  Hom := MeasuredGammaHom
  id := MeasuredGammaHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply MeasuredGammaHom.ext; apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.refl_trans _
  comp_id f := by apply MeasuredGammaHom.ext; apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.trans_refl _
  assoc f g h := by apply MeasuredGammaHom.ext; apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.trans_assoc _ _ _
  inv_comp f := by apply MeasuredGammaHom.ext; apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.symm_trans_self _
  comp_inv f := by apply MeasuredGammaHom.ext; apply GammaHom.ext; apply FamilyBijection.ext; exact Equiv.self_trans_symm _

def measuredFiniteGammaProperty : ObjectProperty (MeasuredGammaObject hc S k) :=
  fun A => finiteGammaProperty A.underlying

abbrev MeasuredFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  (measuredFiniteGammaProperty (hc := hc) (S := S) (k := k)).FullSubcategory

end DiamondIntegral.Section3
