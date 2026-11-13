import «section 3».GammaGroundGammaCodeProductProjections
import «section 3».GammaGroundRelationPullbacks
/-! Pairing actual compatible full-code maps is definable and gives the
categorical cartesian-product universal property on the code category. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l m : ℕ}
variable {A : GammaGroundGammaObject hc ground k} {B : GammaGroundGammaObject hc ground l} {C : GammaGroundGammaObject hc ground m}

def gammaGroundGammaCodePairFunction (F : GammaGroundFamilyMap C.codeLift A.codeLift) (G : GammaGroundFamilyMap C.codeLift B.codeLift)
    (c : C.codeLift.Carrier) : (A.product B).codeLift.Carrier := (A.productCodeEquiv B).symm (F.toFun c, G.toFun c)

theorem gammaGroundGammaCodePairFunction_factor (F : GammaGroundFamilyMap C.codeLift A.codeLift) (G : GammaGroundFamilyMap C.codeLift B.codeLift)
    (c : C.codeLift.Carrier) : A.productCodeEquiv B (gammaGroundGammaCodePairFunction F G c) = (F.toFun c, G.toFun c) :=
  (A.productCodeEquiv B).apply_symm_apply _

theorem gammaGroundGammaCodePairFunction_graph (F : GammaGroundFamilyMap C.codeLift A.codeLift) (G : GammaGroundFamilyMap C.codeLift B.codeLift)
    (i : Fin C.tags) (j : Fin (A.tags * B.tags))
    (c : (codeSpace ((volumeGammaSpace hc).power (Fin m))).Carrier)
    (d : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    gammaGroundFamilyGraph C.codeLift (A.product B).codeLift (gammaGroundGammaCodePairFunction F G) i j c d ↔
      gammaGroundFamilyGraph C.codeLift A.codeLift F.toFun i (finProdFinEquiv.symm j).1 c (gammaCodeLeft d) ∧
      gammaGroundFamilyGraph C.codeLift B.codeLift G.toFun i (finProdFinEquiv.symm j).2 c (gammaCodeRight d) := by
  constructor
  · rintro ⟨cs, ds, hcs, hds, he⟩
    let a := (gammaGroundGammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm j).1) (B.piece (finProdFinEquiv.symm j).2) ds).1
    let b := (gammaGroundGammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm j).1) (B.piece (finProdFinEquiv.symm j).2) ds).2
    have hp := (gammaGroundGammaCodePairFunction_factor F G ⟨i, cs⟩).symm.trans (congrArg (A.productCodeEquiv B) he)
    change (F.toFun ⟨i, cs⟩, G.toFun ⟨i, cs⟩) = (⟨(finProdFinEquiv.symm j).1, a⟩, ⟨(finProdFinEquiv.symm j).2, b⟩) at hp
    exact ⟨⟨cs, a, hcs, (gammaGroundGammaProductCodePieceEquiv_left_val _ _ ds).trans (congrArg gammaCodeLeft hds), congrArg Prod.fst hp⟩,
      ⟨cs, b, hcs, (gammaGroundGammaProductCodePieceEquiv_right_val _ _ ds).trans (congrArg gammaCodeRight hds), congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨cs, a, hcs, ha, hF⟩, ⟨ct, b, hct, hb, hG⟩⟩
    have hct' : ct = cs := Subtype.ext (hct.trans hcs.symm)
    subst ct
    let ds := gammaGroundGammaProductCode (A.piece (finProdFinEquiv.symm j).1) (B.piece (finProdFinEquiv.symm j).2) a b
    refine ⟨cs, ds, hcs, ?_, ?_⟩
    · change gammaCodeAppend a.val b.val = d
      rw [ha, hb, gammaCodeAppend_left_right]
    · apply (A.productCodeEquiv B).injective
      change A.productCodeEquiv B (gammaGroundGammaCodePairFunction F G ⟨i, cs⟩) = A.productCodeEquiv B ⟨j, gammaGroundGammaProductCode _ _ a b⟩
      rw [gammaGroundGammaCodePairFunction_factor, GammaGroundGammaObject.productCodeEquiv_code]
      exact Prod.ext hF hG

def gammaGroundGammaCodePairFamilyMap (F : GammaGroundFamilyMap C.codeLift A.codeLift) (G : GammaGroundFamilyMap C.codeLift B.codeLift) :
    GammaGroundFamilyMap C.codeLift (A.product B).codeLift where
  toFun := gammaGroundGammaCodePairFunction F G
  definable := by
    intro i j
    have hF := gammaGroundRelationDefinable_pullback (F.definable i (finProdFinEquiv.symm j).1)
      (GammaGroundMap.id (GammaGroundDefSet.univ hc ground (codeSpace ((volumeGammaSpace hc).power (Fin m))))) (gammaGroundGammaCodeLeftMap hc ground k l)
    have hG := gammaGroundRelationDefinable_pullback (G.definable i (finProdFinEquiv.symm j).2)
      (GammaGroundMap.id (GammaGroundDefSet.univ hc ground (codeSpace ((volumeGammaSpace hc).power (Fin m))))) (gammaGroundGammaCodeRightMap hc ground k l)
    exact (hF.inter hG).congr (fun z => (gammaGroundGammaCodePairFunction_graph F G i j z.1 z.2).symm)

def gammaGroundGammaCodeProductPair {A B T : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ A.product B where
  map := gammaGroundGammaCodePairFamilyMap f.map g.map
  respects c d h := by
    apply (A.obj.productCarrierEquiv B.obj).injective
    change A.obj.productCarrierEquiv B.obj ((A.obj.product B.obj).decode (gammaGroundGammaCodePairFunction f.map g.map c)) =
      A.obj.productCarrierEquiv B.obj ((A.obj.product B.obj).decode (gammaGroundGammaCodePairFunction f.map g.map d))
    rw [GammaGroundGammaObject.productCodeEquiv_decode, GammaGroundGammaObject.productCodeEquiv_decode,
      gammaGroundGammaCodePairFunction_factor, gammaGroundGammaCodePairFunction_factor]
    exact Prod.ext (f.respects c d h) (g.respects c d h)

theorem gammaGroundGammaCodeProductPair_fst {A B T : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B) :
    gammaGroundGammaCodeProductPair f g ≫ gammaGroundGammaCodeProductFst A B = f := by
  apply GammaGroundGammaCodeMap.ext
  apply GammaGroundFamilyMap.ext
  funext c
  change (A.obj.productCodeEquiv B.obj ((A.obj.productCodeEquiv B.obj).symm (f.map.toFun c, g.map.toFun c))).1 = _
  rw [Equiv.apply_symm_apply]

theorem gammaGroundGammaCodeProductPair_snd {A B T : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B) :
    gammaGroundGammaCodeProductPair f g ≫ gammaGroundGammaCodeProductSnd A B = g := by
  apply GammaGroundGammaCodeMap.ext
  apply GammaGroundFamilyMap.ext
  funext c
  change (A.obj.productCodeEquiv B.obj ((A.obj.productCodeEquiv B.obj).symm (f.map.toFun c, g.map.toFun c))).2 = _
  rw [Equiv.apply_symm_apply]

theorem gammaGroundGammaCodeProductPair_unique {A B T : GammaGroundGammaCodeObject hc ground} (f : T ⟶ A) (g : T ⟶ B)
    (h : T ⟶ A.product B) (hL : h ≫ gammaGroundGammaCodeProductFst A B = f) (hR : h ≫ gammaGroundGammaCodeProductSnd A B = g) :
    h = gammaGroundGammaCodeProductPair f g := by
  apply GammaGroundGammaCodeMap.ext
  apply GammaGroundFamilyMap.ext
  funext c
  apply (A.obj.productCodeEquiv B.obj).injective
  change A.obj.productCodeEquiv B.obj (h.map.toFun c) = A.obj.productCodeEquiv B.obj (gammaGroundGammaCodePairFunction f.map g.map c)
  rw [gammaGroundGammaCodePairFunction_factor]
  exact Prod.ext (congrArg (fun f : T ⟶ A => f.map.toFun c) hL) (congrArg (fun f : T ⟶ B => f.map.toFun c) hR)

end DiamondIntegral.Section3
