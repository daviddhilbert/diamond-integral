import «section 3».GammaGroundMeasuredGammaCodeCoherence
import «section 3».GammaGroundMeasuredGammaRepresentatives
import «section 3».GammaGroundGammaProductLaws
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l j : ℕ}

def gammaGroundMeasuredGammaKPlusCast {k l : ℕ} (h : k = l) (a : GammaGroundMeasuredGammaKPlus hc ground k) : GammaGroundMeasuredGammaKPlus hc ground l := h ▸ a

theorem gammaGroundMeasuredGammaKPlusCast_add {k l : ℕ} (h : k = l) (a b : GammaGroundMeasuredGammaKPlus hc ground k) :
    gammaGroundMeasuredGammaKPlusCast h (a + b) = gammaGroundMeasuredGammaKPlusCast h a + gammaGroundMeasuredGammaKPlusCast h b := by cases h; rfl

theorem gammaGroundMeasuredGammaClass_cast {k l : ℕ} (h : k = l) (A : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaKPlusCast h (gammaGroundMeasuredGammaClass A) = gammaGroundMeasuredGammaClass (h ▸ A) := by cases h; rfl

theorem gammaGroundMeasuredGammaClass_heq_of_castHom {k l : ℕ} (h : k = l) (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (f : GammaGroundMeasuredGammaHom A (h.symm ▸ B)) : HEq (gammaGroundMeasuredGammaClass A) (gammaGroundMeasuredGammaClass B) := by
  have he : gammaGroundMeasuredGammaClass A = gammaGroundMeasuredGammaKPlusCast h.symm (gammaGroundMeasuredGammaClass B) :=
    (gammaGroundMeasuredGammaClass_iso (asIso (show A ⟶ h.symm ▸ B from f))).trans (gammaGroundMeasuredGammaClass_cast h.symm B).symm
  have hh : HEq (gammaGroundMeasuredGammaKPlusCast h.symm (gammaGroundMeasuredGammaClass B)) (gammaGroundMeasuredGammaClass B) := by cases h; rfl
  exact (heq_of_eq he).trans hh

def gammaGroundMeasuredGammaEmptyTagsHom (A : GammaGroundMeasuredGammaObject hc ground k) (h : A.underlying.tags = 0) :
    GammaGroundMeasuredGammaHom A (GammaGroundMeasuredGammaObject.empty hc ground k) where
  underlying := (gammaGroundGammaEmptyTagsIso A.underlying h).hom
  preserves a := (Fin.cast h a.1).elim0

def gammaGroundMeasuredGammaProductEmptyIso (A : GammaGroundMeasuredGammaObject hc ground k) (l : ℕ) :
    A.product (GammaGroundMeasuredGammaObject.empty hc ground l) ≅ GammaGroundMeasuredGammaObject.empty hc ground (k + l) :=
  asIso (show _ ⟶ _ from gammaGroundMeasuredGammaEmptyTagsHom _ (Nat.mul_zero A.underlying.tags))

def gammaGroundMeasuredGammaEmptyProductIso (A : GammaGroundMeasuredGammaObject hc ground l) (k : ℕ) :
    (GammaGroundMeasuredGammaObject.empty hc ground k).product A ≅ GammaGroundMeasuredGammaObject.empty hc ground (k + l) :=
  asIso (show _ ⟶ _ from gammaGroundMeasuredGammaEmptyTagsHom _ (Nat.zero_mul A.underlying.tags))

end DiamondIntegral.Section3
