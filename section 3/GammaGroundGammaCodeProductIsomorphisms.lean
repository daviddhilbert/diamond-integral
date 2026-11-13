import «section 3».GammaGroundGammaCodeProductPairing
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

theorem gammaGroundGammaCodeProductPair_fst_assoc {A B T Z : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B) (h : A ⟶ Z) :
    gammaGroundGammaCodeProductPair f g ≫ gammaGroundGammaCodeProductFst A B ≫ h = f ≫ h := by
  rw [← Category.assoc, gammaGroundGammaCodeProductPair_fst]

theorem gammaGroundGammaCodeProductPair_snd_assoc {A B T Z : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B) (h : B ⟶ Z) :
    gammaGroundGammaCodeProductPair f g ≫ gammaGroundGammaCodeProductSnd A B ≫ h = g ≫ h := by
  rw [← Category.assoc, gammaGroundGammaCodeProductPair_snd]

theorem gammaGroundGammaCodeProduct_hom_ext {A B T : GammaGroundGammaCodeObject hc ground} {f g : T ⟶ A.product B}
    (hL : f ≫ gammaGroundGammaCodeProductFst A B = g ≫ gammaGroundGammaCodeProductFst A B)
    (hR : f ≫ gammaGroundGammaCodeProductSnd A B = g ≫ gammaGroundGammaCodeProductSnd A B) : f = g :=
  (gammaGroundGammaCodeProductPair_unique _ _ f rfl rfl).trans (gammaGroundGammaCodeProductPair_unique _ _ g hL.symm hR.symm).symm

def gammaGroundGammaCodeProductSwap (A B : GammaGroundGammaCodeObject hc ground) : A.product B ⟶ B.product A :=
  gammaGroundGammaCodeProductPair (gammaGroundGammaCodeProductSnd A B) (gammaGroundGammaCodeProductFst A B)

def gammaGroundGammaCodeProductCommIso (A B : GammaGroundGammaCodeObject hc ground) : A.product B ≅ B.product A where
  hom := gammaGroundGammaCodeProductSwap A B
  inv := gammaGroundGammaCodeProductSwap B A
  hom_inv_id := by
    apply gammaGroundGammaCodeProduct_hom_ext <;>
      simp only [gammaGroundGammaCodeProductSwap, Category.assoc, gammaGroundGammaCodeProductPair_fst, gammaGroundGammaCodeProductPair_snd, gammaGroundGammaCodeProductPair_fst_assoc, gammaGroundGammaCodeProductPair_snd_assoc, Category.id_comp]
  inv_hom_id := by
    apply gammaGroundGammaCodeProduct_hom_ext <;>
      simp only [gammaGroundGammaCodeProductSwap, Category.assoc, gammaGroundGammaCodeProductPair_fst, gammaGroundGammaCodeProductPair_snd, gammaGroundGammaCodeProductPair_fst_assoc, gammaGroundGammaCodeProductPair_snd_assoc, Category.id_comp]

def gammaGroundGammaCodeProductAssoc (A B C : GammaGroundGammaCodeObject hc ground) : (A.product B).product C ⟶ A.product (B.product C) :=
  gammaGroundGammaCodeProductPair
    (gammaGroundGammaCodeProductFst (A.product B) C ≫ gammaGroundGammaCodeProductFst A B)
    (gammaGroundGammaCodeProductPair (gammaGroundGammaCodeProductFst (A.product B) C ≫ gammaGroundGammaCodeProductSnd A B)
      (gammaGroundGammaCodeProductSnd (A.product B) C))

def gammaGroundGammaCodeProductAssocInv (A B C : GammaGroundGammaCodeObject hc ground) : A.product (B.product C) ⟶ (A.product B).product C :=
  gammaGroundGammaCodeProductPair
    (gammaGroundGammaCodeProductPair (gammaGroundGammaCodeProductFst A (B.product C))
      (gammaGroundGammaCodeProductSnd A (B.product C) ≫ gammaGroundGammaCodeProductFst B C))
    (gammaGroundGammaCodeProductSnd A (B.product C) ≫ gammaGroundGammaCodeProductSnd B C)

def gammaGroundGammaCodeProductAssocIso (A B C : GammaGroundGammaCodeObject hc ground) : (A.product B).product C ≅ A.product (B.product C) where
  hom := gammaGroundGammaCodeProductAssoc A B C
  inv := gammaGroundGammaCodeProductAssocInv A B C
  hom_inv_id := by
    apply gammaGroundGammaCodeProduct_hom_ext
    · apply gammaGroundGammaCodeProduct_hom_ext <;>
        simp only [gammaGroundGammaCodeProductAssoc, gammaGroundGammaCodeProductAssocInv, Category.assoc,
          gammaGroundGammaCodeProductPair_fst, gammaGroundGammaCodeProductPair_snd, gammaGroundGammaCodeProductPair_fst_assoc, gammaGroundGammaCodeProductPair_snd_assoc, Category.id_comp]
    · simp only [gammaGroundGammaCodeProductAssoc, gammaGroundGammaCodeProductAssocInv, Category.assoc,
        gammaGroundGammaCodeProductPair_fst, gammaGroundGammaCodeProductPair_snd, gammaGroundGammaCodeProductPair_fst_assoc, gammaGroundGammaCodeProductPair_snd_assoc, Category.id_comp]
  inv_hom_id := by
    apply gammaGroundGammaCodeProduct_hom_ext
    · simp only [gammaGroundGammaCodeProductAssoc, gammaGroundGammaCodeProductAssocInv, Category.assoc,
        gammaGroundGammaCodeProductPair_fst, gammaGroundGammaCodeProductPair_snd, gammaGroundGammaCodeProductPair_fst_assoc, gammaGroundGammaCodeProductPair_snd_assoc, Category.id_comp]
    · apply gammaGroundGammaCodeProduct_hom_ext <;>
        simp only [gammaGroundGammaCodeProductAssoc, gammaGroundGammaCodeProductAssocInv, Category.assoc,
          gammaGroundGammaCodeProductPair_fst, gammaGroundGammaCodeProductPair_snd, gammaGroundGammaCodeProductPair_fst_assoc, gammaGroundGammaCodeProductPair_snd_assoc, Category.id_comp]

end DiamondIntegral.Section3
