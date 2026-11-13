import «section 3».GammaGroundGammaCodeProductUnits
import «section 3».GammaGroundGammaRepresentatives
import «section 3».GammaGroundGammaProductMorphisms
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

def gammaGroundGammaProductCommHom (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    GammaGroundGammaHom (A.product B) ((Nat.add_comm k l).symm ▸ B.product A) :=
  gammaGroundGammaHomOfCodeIso (gammaGroundGammaCodeProductCommIso (⟨k, A⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B⟩) (Nat.add_comm k l)

def gammaGroundGammaProductAssocHom (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) (D : GammaGroundGammaObject hc ground j) :
    GammaGroundGammaHom ((A.product B).product D) ((Nat.add_assoc k l j).symm ▸ A.product (B.product D)) :=
  gammaGroundGammaHomOfCodeIso (gammaGroundGammaCodeProductAssocIso (⟨k, A⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B⟩ ⟨j, D⟩) (Nat.add_assoc k l j)

def gammaGroundGammaProductRightUnitHom (A : GammaGroundGammaObject hc ground k) : GammaGroundGammaHom (A.product (GammaGroundGammaObject.unit hc ground)) A :=
  gammaGroundGammaHomOfCodeIso (gammaGroundGammaCodeProductRightUnitIso (⟨k, A⟩ : GammaGroundGammaCodeObject hc ground)) (Nat.add_zero k)

def gammaGroundGammaKPlusCast {k l : ℕ} (h : k = l) (a : GammaGroundGammaKPlus hc ground k) : GammaGroundGammaKPlus hc ground l := h ▸ a

theorem gammaGroundGammaKPlusCast_add {k l : ℕ} (h : k = l) (a b : GammaGroundGammaKPlus hc ground k) :
    gammaGroundGammaKPlusCast h (a + b) = gammaGroundGammaKPlusCast h a + gammaGroundGammaKPlusCast h b := by cases h; rfl

theorem gammaGroundGammaClass_cast {k l : ℕ} (h : k = l) (A : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaKPlusCast h (gammaGroundGammaClass A) = gammaGroundGammaClass (h ▸ A) := by cases h; rfl

theorem gammaGroundGammaClass_heq_of_castHom {k l : ℕ} (h : k = l) (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (f : GammaGroundGammaHom A (h.symm ▸ B)) : HEq (gammaGroundGammaClass A) (gammaGroundGammaClass B) := by
  have he : gammaGroundGammaClass A = gammaGroundGammaKPlusCast h.symm (gammaGroundGammaClass B) :=
    (gammaGroundGammaClass_iso (asIso (show A ⟶ h.symm ▸ B from f))).trans (gammaGroundGammaClass_cast h.symm B).symm
  have hh : HEq (gammaGroundGammaKPlusCast h.symm (gammaGroundGammaClass B)) (gammaGroundGammaClass B) := by cases h; rfl
  exact (heq_of_eq he).trans hh

def gammaGroundGammaEmptyTagsIso (A : GammaGroundGammaObject hc ground k) (h : A.tags = 0) : A ≅ GammaGroundGammaObject.empty hc ground k :=
  asIso (show A ⟶ GammaGroundGammaObject.empty hc ground k from gammaGroundGammaTagHom _ _ (finCongr h) (fun i => (finCongr h i).elim0))

def gammaGroundGammaProductEmptyIso (A : GammaGroundGammaObject hc ground k) (l : ℕ) :
    A.product (GammaGroundGammaObject.empty hc ground l) ≅ GammaGroundGammaObject.empty hc ground (k + l) :=
  gammaGroundGammaEmptyTagsIso _ (Nat.mul_zero A.tags)

def gammaGroundGammaEmptyProductIso (A : GammaGroundGammaObject hc ground l) (k : ℕ) :
    (GammaGroundGammaObject.empty hc ground k).product A ≅ GammaGroundGammaObject.empty hc ground (k + l) :=
  gammaGroundGammaEmptyTagsIso _ (Nat.zero_mul A.tags)

end DiamondIntegral.Section3
