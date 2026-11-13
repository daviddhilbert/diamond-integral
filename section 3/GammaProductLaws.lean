import «section 3».GammaCodeProductUnits
import «section 3».GammaRepresentatives
import «section 3».GammaProductMorphisms

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

def gammaProductCommHom (A : GammaObject hc S k) (B : GammaObject hc S l) :
    GammaHom (A.product B) ((Nat.add_comm k l).symm ▸ B.product A) :=
  gammaHomOfCodeIso (gammaCodeProductCommIso (⟨k, A⟩ : GammaCodeObject hc S) ⟨l, B⟩) (Nat.add_comm k l)

def gammaProductAssocHom (A : GammaObject hc S k) (B : GammaObject hc S l) (D : GammaObject hc S j) :
    GammaHom ((A.product B).product D) ((Nat.add_assoc k l j).symm ▸ A.product (B.product D)) :=
  gammaHomOfCodeIso (gammaCodeProductAssocIso (⟨k, A⟩ : GammaCodeObject hc S) ⟨l, B⟩ ⟨j, D⟩) (Nat.add_assoc k l j)

def gammaProductRightUnitHom (A : GammaObject hc S k) : GammaHom (A.product (GammaObject.unit hc S)) A :=
  gammaHomOfCodeIso (gammaCodeProductRightUnitIso (⟨k, A⟩ : GammaCodeObject hc S)) (Nat.add_zero k)

def gammaKPlusCast {k l : ℕ} (h : k = l) (a : GammaKPlus hc S k) : GammaKPlus hc S l := h ▸ a

theorem gammaKPlusCast_add {k l : ℕ} (h : k = l) (a b : GammaKPlus hc S k) :
    gammaKPlusCast h (a + b) = gammaKPlusCast h a + gammaKPlusCast h b := by cases h; rfl

theorem gammaClass_cast {k l : ℕ} (h : k = l) (A : GammaObject hc S k) :
    gammaKPlusCast h (gammaClass A) = gammaClass (h ▸ A) := by cases h; rfl

theorem gammaClass_heq_of_castHom {k l : ℕ} (h : k = l) (A : GammaObject hc S k) (B : GammaObject hc S l)
    (f : GammaHom A (h.symm ▸ B)) : HEq (gammaClass A) (gammaClass B) := by
  have he : gammaClass A = gammaKPlusCast h.symm (gammaClass B) :=
    (gammaClass_iso (asIso (show A ⟶ h.symm ▸ B from f))).trans (gammaClass_cast h.symm B).symm
  have hh : HEq (gammaKPlusCast h.symm (gammaClass B)) (gammaClass B) := by cases h; rfl
  exact (heq_of_eq he).trans hh

def gammaEmptyTagsIso (A : GammaObject hc S k) (h : A.tags = 0) : A ≅ GammaObject.empty hc S k :=
  asIso (show A ⟶ GammaObject.empty hc S k from gammaTagHom _ _ (finCongr h) (fun i => (finCongr h i).elim0))

def gammaProductEmptyIso (A : GammaObject hc S k) (l : ℕ) :
    A.product (GammaObject.empty hc S l) ≅ GammaObject.empty hc S (k + l) :=
  gammaEmptyTagsIso _ (Nat.mul_zero A.tags)

def gammaEmptyProductIso (A : GammaObject hc S l) (k : ℕ) :
    (GammaObject.empty hc S k).product A ≅ GammaObject.empty hc S (k + l) :=
  gammaEmptyTagsIso _ (Nat.zero_mul A.tags)

end DiamondIntegral.Section3
