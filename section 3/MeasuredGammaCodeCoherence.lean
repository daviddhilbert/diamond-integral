import «section 3».MeasuredGammaProductMorphisms
import «section 3».GammaCodeProductUnits

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l j : ℕ}

def measuredGammaHomOfCodeIso {A : MeasuredGammaObject hc S k} {B : MeasuredGammaObject hc S l}
    (e : (⟨k, A.underlying⟩ : GammaCodeObject hc S) ≅ ⟨l, B.underlying⟩) (h : k = l)
    (hW : ∀ c, A.combinedWeight (A.underlying.decode c) =
      B.combinedWeight (B.underlying.decode (e.hom.map.toFun c))) :
    MeasuredGammaHom A (h.symm ▸ B) := by
  subst l
  exact measuredGammaHomOfCodes (gammaCodeBijectionOfIso e) (gammaCodeIso_kernel e) hW

theorem gammaCodePair_fst_apply {A B T : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B)
    (c : T.obj.codeLift.Carrier) :
    (gammaCodeProductFst A B).map.toFun ((gammaCodeProductPair f g).map.toFun c) = f.map.toFun c :=
  congrArg (fun h : T ⟶ A => h.map.toFun c) (gammaCodeProductPair_fst f g)

theorem gammaCodePair_snd_apply {A B T : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B)
    (c : T.obj.codeLift.Carrier) :
    (gammaCodeProductSnd A B).map.toFun ((gammaCodeProductPair f g).map.toFun c) = g.map.toFun c :=
  congrArg (fun h : T ⟶ B => h.map.toFun c) (gammaCodeProductPair_snd f g)

theorem gammaCodeComp_apply {A B D : GammaCodeObject hc S} (f : A ⟶ B) (g : B ⟶ D)
    (c : A.obj.codeLift.Carrier) : (f ≫ g).map.toFun c = g.map.toFun (f.map.toFun c) := rfl

def MeasuredGammaObject.codeCombined (A : MeasuredGammaObject hc S k)
    (c : A.underlying.codeLift.Carrier) := A.combinedWeight (A.underlying.decode c)

theorem measuredGammaCodeCombined_product (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (c : (A.underlying.product B.underlying).codeLift.Carrier) :
    (A.product B).codeCombined c =
      A.codeCombined ((gammaCodeProductFst (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩).map.toFun c) *
        B.codeCombined ((gammaCodeProductSnd (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩).map.toFun c) := by
  rw [MeasuredGammaObject.codeCombined, measuredGammaProduct_factor, GammaObject.productCodeEquiv_decode]
  rfl

def measuredGammaProductCommHom (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l) :
    MeasuredGammaHom (A.product B) ((Nat.add_comm k l).symm ▸ B.product A) :=
  measuredGammaHomOfCodeIso
    (gammaCodeProductCommIso (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩)
    (Nat.add_comm k l) (by
      intro c
      change (A.product B).codeCombined c = (B.product A).codeCombined
        ((gammaCodeProductPair (gammaCodeProductSnd (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩)
          (gammaCodeProductFst (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩)).map.toFun c)
      rw [measuredGammaCodeCombined_product, measuredGammaCodeCombined_product,
        gammaCodePair_fst_apply, gammaCodePair_snd_apply]
      exact mul_comm _ _)

def measuredGammaProductAssocHom (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (D : MeasuredGammaObject hc S j) :
    MeasuredGammaHom ((A.product B).product D) ((Nat.add_assoc k l j).symm ▸ A.product (B.product D)) :=
  measuredGammaHomOfCodeIso
    (gammaCodeProductAssocIso (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩ ⟨j, D.underlying⟩)
    (Nat.add_assoc k l j) (by
      intro c
      change ((A.product B).product D).codeCombined c =
        (A.product (B.product D)).codeCombined ((gammaCodeProductAssoc
          (⟨k, A.underlying⟩ : GammaCodeObject hc S) ⟨l, B.underlying⟩ ⟨j, D.underlying⟩).map.toFun c)
      simp only [measuredGammaCodeCombined_product, gammaCodeProductAssoc,
        gammaCodePair_fst_apply, gammaCodePair_snd_apply, gammaCodeComp_apply]
      exact mul_assoc _ _ _)

theorem measuredGammaUnit_combined (a : (GammaObject.unit (M := M) hc S).Carrier) :
    (MeasuredGammaObject.unit hc S).combinedWeight a = 1 := by
  change gammaFormValue (gammaOneForm hc _) _ * (∏ i : Fin 0, _) = 1
  rw [gammaOneForm_value, Fin.prod_univ_zero, mul_one]

def measuredGammaProductRightUnitHom (A : MeasuredGammaObject hc S k) :
    MeasuredGammaHom (A.product (MeasuredGammaObject.unit hc S)) A :=
  measuredGammaHomOfCodeIso (gammaCodeProductRightUnitIso (⟨k, A.underlying⟩ : GammaCodeObject hc S))
    (Nat.add_zero k) (by
      intro c
      change (A.product (MeasuredGammaObject.unit hc S)).codeCombined c =
        A.codeCombined ((gammaCodeProductFst (⟨k, A.underlying⟩ : GammaCodeObject hc S)
          (GammaCodeObject.unit hc S)).map.toFun c)
      rw [measuredGammaCodeCombined_product]
      change _ * (MeasuredGammaObject.unit hc S).combinedWeight _ = _
      rw [measuredGammaUnit_combined, mul_one]
      rfl)

end DiamondIntegral.Section3
