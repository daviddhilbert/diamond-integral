import «section 3».GammaCodeProductProjections

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l m : ℕ}
variable {A : GammaObject hc S k} {B : GammaObject hc S l} {C : GammaObject hc S m}

def gammaCodePairFunction (F : FamilyMap C.codeLift A.codeLift) (G : FamilyMap C.codeLift B.codeLift)
    (c : C.codeLift.Carrier) : (A.product B).codeLift.Carrier := (A.productCodeEquiv B).symm (F.toFun c, G.toFun c)

theorem gammaCodePairFunction_factor (F : FamilyMap C.codeLift A.codeLift) (G : FamilyMap C.codeLift B.codeLift)
    (c : C.codeLift.Carrier) : A.productCodeEquiv B (gammaCodePairFunction F G c) = (F.toFun c, G.toFun c) :=
  (A.productCodeEquiv B).apply_symm_apply _

theorem gammaCodePairFunction_graph (F : FamilyMap C.codeLift A.codeLift) (G : FamilyMap C.codeLift B.codeLift)
    (i : Fin C.tags) (j : Fin (A.tags * B.tags))
    (c : (codeSpace ((volumeGammaSpace hc).power (Fin m))).Carrier)
    (d : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    familyGraph C.codeLift (A.product B).codeLift (gammaCodePairFunction F G) i j c d ↔
      familyGraph C.codeLift A.codeLift F.toFun i (finProdFinEquiv.symm j).1 c (gammaCodeLeft d) ∧
      familyGraph C.codeLift B.codeLift G.toFun i (finProdFinEquiv.symm j).2 c (gammaCodeRight d) := by
  constructor
  · rintro ⟨cs, ds, hcs, hds, he⟩
    let a := (gammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm j).1) (B.piece (finProdFinEquiv.symm j).2) ds).1
    let b := (gammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm j).1) (B.piece (finProdFinEquiv.symm j).2) ds).2
    have hp := (gammaCodePairFunction_factor F G ⟨i, cs⟩).symm.trans (congrArg (A.productCodeEquiv B) he)
    change (F.toFun ⟨i, cs⟩, G.toFun ⟨i, cs⟩) = (⟨(finProdFinEquiv.symm j).1, a⟩, ⟨(finProdFinEquiv.symm j).2, b⟩) at hp
    exact ⟨⟨cs, a, hcs, (gammaProductCodePieceEquiv_left_val _ _ ds).trans (congrArg gammaCodeLeft hds), congrArg Prod.fst hp⟩,
      ⟨cs, b, hcs, (gammaProductCodePieceEquiv_right_val _ _ ds).trans (congrArg gammaCodeRight hds), congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨cs, a, hcs, ha, hF⟩, ⟨ct, b, hct, hb, hG⟩⟩
    have hct' : ct = cs := Subtype.ext (hct.trans hcs.symm)
    subst ct
    let ds := gammaProductCode (A.piece (finProdFinEquiv.symm j).1) (B.piece (finProdFinEquiv.symm j).2) a b
    refine ⟨cs, ds, hcs, ?_, ?_⟩
    · change gammaCodeAppend a.val b.val = d
      rw [ha, hb, gammaCodeAppend_left_right]
    · apply (A.productCodeEquiv B).injective
      change A.productCodeEquiv B (gammaCodePairFunction F G ⟨i, cs⟩) = A.productCodeEquiv B ⟨j, gammaProductCode _ _ a b⟩
      rw [gammaCodePairFunction_factor, GammaObject.productCodeEquiv_code]
      exact Prod.ext hF hG

def gammaCodePairFamilyMap (F : FamilyMap C.codeLift A.codeLift) (G : FamilyMap C.codeLift B.codeLift) :
    FamilyMap C.codeLift (A.product B).codeLift where
  toFun := gammaCodePairFunction F G
  definable := by
    intro i j
    have hF := relationDefinable_pullback (F.definable i (finProdFinEquiv.symm j).1)
      (Map.id (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin m))) S)) (gammaCodeLeftMap hc S k l)
    have hG := relationDefinable_pullback (G.definable i (finProdFinEquiv.symm j).2)
      (Map.id (DefSet.univ (codeSpace ((volumeGammaSpace hc).power (Fin m))) S)) (gammaCodeRightMap hc S k l)
    exact (hF.inter _ _ hG).congr _ _ (fun c d => (gammaCodePairFunction_graph F G i j c d).symm)

def gammaCodeProductPair {A B T : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ A.product B where
  map := gammaCodePairFamilyMap f.map g.map
  respects c d h := by
    apply (A.obj.productCarrierEquiv B.obj).injective
    change A.obj.productCarrierEquiv B.obj ((A.obj.product B.obj).decode (gammaCodePairFunction f.map g.map c)) =
      A.obj.productCarrierEquiv B.obj ((A.obj.product B.obj).decode (gammaCodePairFunction f.map g.map d))
    rw [GammaObject.productCodeEquiv_decode, GammaObject.productCodeEquiv_decode,
      gammaCodePairFunction_factor, gammaCodePairFunction_factor]
    exact Prod.ext (f.respects c d h) (g.respects c d h)

theorem gammaCodeProductPair_fst {A B T : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B) :
    gammaCodeProductPair f g ≫ gammaCodeProductFst A B = f := by
  apply GammaCodeMap.ext
  apply FamilyMap.ext
  funext c
  change (A.obj.productCodeEquiv B.obj ((A.obj.productCodeEquiv B.obj).symm (f.map.toFun c, g.map.toFun c))).1 = _
  rw [Equiv.apply_symm_apply]

theorem gammaCodeProductPair_snd {A B T : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B) :
    gammaCodeProductPair f g ≫ gammaCodeProductSnd A B = g := by
  apply GammaCodeMap.ext
  apply FamilyMap.ext
  funext c
  change (A.obj.productCodeEquiv B.obj ((A.obj.productCodeEquiv B.obj).symm (f.map.toFun c, g.map.toFun c))).2 = _
  rw [Equiv.apply_symm_apply]

theorem gammaCodeProductPair_unique {A B T : GammaCodeObject hc S} (f : T ⟶ A) (g : T ⟶ B)
    (h : T ⟶ A.product B) (hL : h ≫ gammaCodeProductFst A B = f) (hR : h ≫ gammaCodeProductSnd A B = g) :
    h = gammaCodeProductPair f g := by
  apply GammaCodeMap.ext
  apply FamilyMap.ext
  funext c
  apply (A.obj.productCodeEquiv B.obj).injective
  change A.obj.productCodeEquiv B.obj (h.map.toFun c) = A.obj.productCodeEquiv B.obj (gammaCodePairFunction f.map g.map c)
  rw [gammaCodePairFunction_factor]
  exact Prod.ext (congrArg (fun f : T ⟶ A => f.map.toFun c) hL) (congrArg (fun f : T ⟶ B => f.map.toFun c) hR)

end DiamondIntegral.Section3
