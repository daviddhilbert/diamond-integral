import «section 3».MeasuredGammaCodeCoherence
import «section 3».MeasuredGammaRepresentatives
import «section 3».GammaProductLaws

/-! Actual Gamma product symmetry, associativity and unit morphisms,
with explicit degree casts rather than implicit rank identifications. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l j : ℕ}

def measuredGammaKPlusCast {k l : ℕ} (h : k = l) (a : MeasuredGammaKPlus hc S k) : MeasuredGammaKPlus hc S l := h ▸ a

theorem measuredGammaKPlusCast_add {k l : ℕ} (h : k = l) (a b : MeasuredGammaKPlus hc S k) :
    measuredGammaKPlusCast h (a + b) = measuredGammaKPlusCast h a + measuredGammaKPlusCast h b := by cases h; rfl

theorem measuredGammaClass_cast {k l : ℕ} (h : k = l) (A : MeasuredGammaObject hc S k) :
    measuredGammaKPlusCast h (measuredGammaClass A) = measuredGammaClass (h ▸ A) := by cases h; rfl

theorem measuredGammaClass_heq_of_castHom {k l : ℕ} (h : k = l) (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (f : MeasuredGammaHom A (h.symm ▸ B)) : HEq (measuredGammaClass A) (measuredGammaClass B) := by
  have he : measuredGammaClass A = measuredGammaKPlusCast h.symm (measuredGammaClass B) :=
    (measuredGammaClass_iso (asIso (show A ⟶ h.symm ▸ B from f))).trans (measuredGammaClass_cast h.symm B).symm
  have hh : HEq (measuredGammaKPlusCast h.symm (measuredGammaClass B)) (measuredGammaClass B) := by cases h; rfl
  exact (heq_of_eq he).trans hh

def measuredGammaEmptyTagsHom (A : MeasuredGammaObject hc S k) (h : A.underlying.tags = 0) :
    MeasuredGammaHom A (MeasuredGammaObject.empty hc S k) where
  underlying := (gammaEmptyTagsIso A.underlying h).hom
  preserves a := (Fin.cast h a.1).elim0

def measuredGammaProductEmptyIso (A : MeasuredGammaObject hc S k) (l : ℕ) :
    A.product (MeasuredGammaObject.empty hc S l) ≅ MeasuredGammaObject.empty hc S (k + l) :=
  asIso (show _ ⟶ _ from measuredGammaEmptyTagsHom _ (Nat.mul_zero A.underlying.tags))

def measuredGammaEmptyProductIso (A : MeasuredGammaObject hc S l) (k : ℕ) :
    (MeasuredGammaObject.empty hc S k).product A ≅ MeasuredGammaObject.empty hc S (k + l) :=
  asIso (show _ ⟶ _ from measuredGammaEmptyTagsHom _ (Nat.zero_mul A.underlying.tags))

end DiamondIntegral.Section3
