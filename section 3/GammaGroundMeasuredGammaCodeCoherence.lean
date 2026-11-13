import «section 3».GammaGroundMeasuredGammaProductMorphisms
import «section 3».GammaGroundGammaCodeProductUnits
/-! Product coherence for measured Gamma objects is checked on every
RV code, then descends with its original complete decoding relation. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l j : ℕ}

def gammaGroundMeasuredGammaHomOfCodeIso {A : GammaGroundMeasuredGammaObject hc ground k} {B : GammaGroundMeasuredGammaObject hc ground l}
    (e : (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ≅ ⟨l, B.underlying⟩) (h : k = l)
    (hW : ∀ c, A.combinedWeight (A.underlying.decode c) =
      B.combinedWeight (B.underlying.decode (e.hom.map.toFun c))) :
    GammaGroundMeasuredGammaHom A (h.symm ▸ B) := by
  subst l
  exact gammaGroundMeasuredGammaHomOfCodes (gammaGroundGammaCodeBijectionOfIso e) (gammaGroundGammaCodeIso_kernel e) hW

theorem gammaGroundGammaCodePair_fst_apply {A B T : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B)
    (c : T.obj.codeLift.Carrier) :
    (gammaGroundGammaCodeProductFst A B).map.toFun ((gammaGroundGammaCodeProductPair f g).map.toFun c) = f.map.toFun c :=
  congrArg (fun h : T ⟶ A => h.map.toFun c) (gammaGroundGammaCodeProductPair_fst f g)

theorem gammaGroundGammaCodePair_snd_apply {A B T : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B)
    (c : T.obj.codeLift.Carrier) :
    (gammaGroundGammaCodeProductSnd A B).map.toFun ((gammaGroundGammaCodeProductPair f g).map.toFun c) = g.map.toFun c :=
  congrArg (fun h : T ⟶ B => h.map.toFun c) (gammaGroundGammaCodeProductPair_snd f g)

theorem gammaGroundGammaCodeComp_apply {A B D : GammaGroundGammaCodeObject hc ground} (f : A ⟶ B) (g : B ⟶ D)
    (c : A.obj.codeLift.Carrier) : (f ≫ g).map.toFun c = g.map.toFun (f.map.toFun c) := rfl

def GammaGroundMeasuredGammaObject.codeCombined (A : GammaGroundMeasuredGammaObject hc ground k)
    (c : A.underlying.codeLift.Carrier) := A.combinedWeight (A.underlying.decode c)

theorem gammaGroundMeasuredGammaCodeCombined_product (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (c : (A.underlying.product B.underlying).codeLift.Carrier) :
    (A.product B).codeCombined c =
      A.codeCombined ((gammaGroundGammaCodeProductFst (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩).map.toFun c) *
        B.codeCombined ((gammaGroundGammaCodeProductSnd (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩).map.toFun c) := by
  rw [GammaGroundMeasuredGammaObject.codeCombined, gammaGroundMeasuredGammaProduct_factor, GammaGroundGammaObject.productCodeEquiv_decode]
  rfl

def gammaGroundMeasuredGammaProductCommHom (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l) :
    GammaGroundMeasuredGammaHom (A.product B) ((Nat.add_comm k l).symm ▸ B.product A) :=
  gammaGroundMeasuredGammaHomOfCodeIso
    (gammaGroundGammaCodeProductCommIso (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩)
    (Nat.add_comm k l) (by
      intro c
      change (A.product B).codeCombined c = (B.product A).codeCombined
        ((gammaGroundGammaCodeProductPair (gammaGroundGammaCodeProductSnd (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩)
          (gammaGroundGammaCodeProductFst (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩)).map.toFun c)
      rw [gammaGroundMeasuredGammaCodeCombined_product, gammaGroundMeasuredGammaCodeCombined_product,
        gammaGroundGammaCodePair_fst_apply, gammaGroundGammaCodePair_snd_apply]
      exact mul_comm _ _)

def gammaGroundMeasuredGammaProductAssocHom (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (D : GammaGroundMeasuredGammaObject hc ground j) :
    GammaGroundMeasuredGammaHom ((A.product B).product D) ((Nat.add_assoc k l j).symm ▸ A.product (B.product D)) :=
  gammaGroundMeasuredGammaHomOfCodeIso
    (gammaGroundGammaCodeProductAssocIso (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩ ⟨j, D.underlying⟩)
    (Nat.add_assoc k l j) (by
      intro c
      change ((A.product B).product D).codeCombined c =
        (A.product (B.product D)).codeCombined ((gammaGroundGammaCodeProductAssoc
          (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground) ⟨l, B.underlying⟩ ⟨j, D.underlying⟩).map.toFun c)
      simp only [gammaGroundMeasuredGammaCodeCombined_product, gammaGroundGammaCodeProductAssoc,
        gammaGroundGammaCodePair_fst_apply, gammaGroundGammaCodePair_snd_apply, gammaGroundGammaCodeComp_apply]
      exact mul_assoc _ _ _)

theorem gammaGroundMeasuredGammaUnit_combined (a : (GammaGroundGammaObject.unit (M := M) hc ground).Carrier) :
    (GammaGroundMeasuredGammaObject.unit hc ground).combinedWeight a = 1 := by
  change gammaGroundFormValue (gammaGroundOneForm _) _ * (∏ i : Fin 0, _) = 1
  rw [gammaGroundOneForm_value, Fin.prod_univ_zero, mul_one]

def gammaGroundMeasuredGammaProductRightUnitHom (A : GammaGroundMeasuredGammaObject hc ground k) :
    GammaGroundMeasuredGammaHom (A.product (GammaGroundMeasuredGammaObject.unit hc ground)) A :=
  gammaGroundMeasuredGammaHomOfCodeIso (gammaGroundGammaCodeProductRightUnitIso (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground))
    (Nat.add_zero k) (by
      intro c
      change (A.product (GammaGroundMeasuredGammaObject.unit hc ground)).codeCombined c =
        A.codeCombined ((gammaGroundGammaCodeProductFst (⟨k, A.underlying⟩ : GammaGroundGammaCodeObject hc ground)
          (GammaGroundGammaCodeObject.unit hc ground)).map.toFun c)
      rw [gammaGroundMeasuredGammaCodeCombined_product]
      change _ * (GammaGroundMeasuredGammaObject.unit hc ground).combinedWeight _ = _
      rw [gammaGroundMeasuredGammaUnit_combined, mul_one]
      rfl)

end DiamondIntegral.Section3
