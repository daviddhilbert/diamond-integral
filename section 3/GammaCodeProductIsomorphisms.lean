import «section 3».GammaCodeProductPairing

/-! Actual full-code product symmetries and associativity isomorphisms,
built only from definable projections and pairing. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

theorem gammaCodeProductPair_fst_assoc {A B T Z : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B) (h : A ⟶ Z) :
    gammaCodeProductPair f g ≫ gammaCodeProductFst A B ≫ h = f ≫ h := by
  rw [← Category.assoc, gammaCodeProductPair_fst]

theorem gammaCodeProductPair_snd_assoc {A B T Z : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B) (h : B ⟶ Z) :
    gammaCodeProductPair f g ≫ gammaCodeProductSnd A B ≫ h = g ≫ h := by
  rw [← Category.assoc, gammaCodeProductPair_snd]

theorem gammaCodeProduct_hom_ext {A B T : GammaCodeObject hc S} {f g : T ⟶ A.product B}
    (hL : f ≫ gammaCodeProductFst A B = g ≫ gammaCodeProductFst A B)
    (hR : f ≫ gammaCodeProductSnd A B = g ≫ gammaCodeProductSnd A B) : f = g :=
  (gammaCodeProductPair_unique _ _ f rfl rfl).trans (gammaCodeProductPair_unique _ _ g hL.symm hR.symm).symm

def gammaCodeProductSwap (A B : GammaCodeObject hc S) : A.product B ⟶ B.product A :=
  gammaCodeProductPair (gammaCodeProductSnd A B) (gammaCodeProductFst A B)

def gammaCodeProductCommIso (A B : GammaCodeObject hc S) : A.product B ≅ B.product A where
  hom := gammaCodeProductSwap A B
  inv := gammaCodeProductSwap B A
  hom_inv_id := by
    apply gammaCodeProduct_hom_ext <;>
      simp only [gammaCodeProductSwap, Category.assoc, gammaCodeProductPair_fst, gammaCodeProductPair_snd, gammaCodeProductPair_fst_assoc, gammaCodeProductPair_snd_assoc, Category.id_comp]
  inv_hom_id := by
    apply gammaCodeProduct_hom_ext <;>
      simp only [gammaCodeProductSwap, Category.assoc, gammaCodeProductPair_fst, gammaCodeProductPair_snd, gammaCodeProductPair_fst_assoc, gammaCodeProductPair_snd_assoc, Category.id_comp]

def gammaCodeProductAssoc (A B C : GammaCodeObject hc S) : (A.product B).product C ⟶ A.product (B.product C) :=
  gammaCodeProductPair
    (gammaCodeProductFst (A.product B) C ≫ gammaCodeProductFst A B)
    (gammaCodeProductPair (gammaCodeProductFst (A.product B) C ≫ gammaCodeProductSnd A B)
      (gammaCodeProductSnd (A.product B) C))

def gammaCodeProductAssocInv (A B C : GammaCodeObject hc S) : A.product (B.product C) ⟶ (A.product B).product C :=
  gammaCodeProductPair
    (gammaCodeProductPair (gammaCodeProductFst A (B.product C))
      (gammaCodeProductSnd A (B.product C) ≫ gammaCodeProductFst B C))
    (gammaCodeProductSnd A (B.product C) ≫ gammaCodeProductSnd B C)

def gammaCodeProductAssocIso (A B C : GammaCodeObject hc S) : (A.product B).product C ≅ A.product (B.product C) where
  hom := gammaCodeProductAssoc A B C
  inv := gammaCodeProductAssocInv A B C
  hom_inv_id := by
    apply gammaCodeProduct_hom_ext
    · apply gammaCodeProduct_hom_ext <;>
        simp only [gammaCodeProductAssoc, gammaCodeProductAssocInv, Category.assoc,
          gammaCodeProductPair_fst, gammaCodeProductPair_snd, gammaCodeProductPair_fst_assoc, gammaCodeProductPair_snd_assoc, Category.id_comp]
    · simp only [gammaCodeProductAssoc, gammaCodeProductAssocInv, Category.assoc,
        gammaCodeProductPair_fst, gammaCodeProductPair_snd, gammaCodeProductPair_fst_assoc, gammaCodeProductPair_snd_assoc, Category.id_comp]
  inv_hom_id := by
    apply gammaCodeProduct_hom_ext
    · simp only [gammaCodeProductAssoc, gammaCodeProductAssocInv, Category.assoc,
        gammaCodeProductPair_fst, gammaCodeProductPair_snd, gammaCodeProductPair_fst_assoc, gammaCodeProductPair_snd_assoc, Category.id_comp]
    · apply gammaCodeProduct_hom_ext <;>
        simp only [gammaCodeProductAssoc, gammaCodeProductAssocInv, Category.assoc,
          gammaCodeProductPair_fst, gammaCodeProductPair_snd, gammaCodeProductPair_fst_assoc, gammaCodeProductPair_snd_assoc, Category.id_comp]

end DiamondIntegral.Section3
