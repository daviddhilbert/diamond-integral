import «section 3».GammaGroundGammaCodeProjections
import «section 3».GammaGroundRelationPullbacks
/-! Products of arbitrary definable full-code gammaGroundFamily bijections remain
definable on the actual concatenated Gamma code families. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}
variable {A A' : GammaGroundGammaObject hc ground k} {B B' : GammaGroundGammaObject hc ground l}

def gammaGroundGammaProductCodeFunctionEquiv (F : GammaGroundFamilyBijection A.codeLift A'.codeLift)
    (G : GammaGroundFamilyBijection B.codeLift B'.codeLift) :
    (A.product B).codeLift.Carrier ≃ (A'.product B').codeLift.Carrier :=
  (A.productCodeEquiv B).trans ((Equiv.prodCongr F.equiv G.equiv).trans (A'.productCodeEquiv B').symm)

theorem gammaGroundGammaProductCodeFunctionEquiv_factor (F : GammaGroundFamilyBijection A.codeLift A'.codeLift)
    (G : GammaGroundFamilyBijection B.codeLift B'.codeLift) (c : (A.product B).codeLift.Carrier) :
    A'.productCodeEquiv B' (gammaGroundGammaProductCodeFunctionEquiv F G c) =
      (F.equiv (A.productCodeEquiv B c).1, G.equiv (A.productCodeEquiv B c).2) :=
  (A'.productCodeEquiv B').apply_symm_apply _

theorem gammaGroundGammaProductCodeFunctionEquiv_graph (F : GammaGroundFamilyBijection A.codeLift A'.codeLift)
    (G : GammaGroundFamilyBijection B.codeLift B'.codeLift) (i : Fin (A.tags * B.tags)) (j : Fin (A'.tags * B'.tags))
    (c d : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    gammaGroundFamilyGraph (A.product B).codeLift (A'.product B').codeLift (gammaGroundGammaProductCodeFunctionEquiv F G) i j c d ↔
      gammaGroundFamilyGraph A.codeLift A'.codeLift F.equiv (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
        (gammaCodeLeft c) (gammaCodeLeft d) ∧
      gammaGroundFamilyGraph B.codeLift B'.codeLift G.equiv (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
        (gammaCodeRight c) (gammaCodeRight d) := by
  constructor
  · rintro ⟨cs, ds, hc', hd', he⟩
    let ca := (gammaGroundGammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) cs).1
    let cb := (gammaGroundGammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) cs).2
    let da := (gammaGroundGammaProductCodePieceEquiv (A'.piece (finProdFinEquiv.symm j).1) (B'.piece (finProdFinEquiv.symm j).2) ds).1
    let db := (gammaGroundGammaProductCodePieceEquiv (A'.piece (finProdFinEquiv.symm j).1) (B'.piece (finProdFinEquiv.symm j).2) ds).2
    have hp := (gammaGroundGammaProductCodeFunctionEquiv_factor F G ⟨i, cs⟩).symm.trans
      (congrArg (A'.productCodeEquiv B') he)
    change (F.equiv ⟨(finProdFinEquiv.symm i).1, ca⟩, G.equiv ⟨(finProdFinEquiv.symm i).2, cb⟩) =
      (⟨(finProdFinEquiv.symm j).1, da⟩, ⟨(finProdFinEquiv.symm j).2, db⟩) at hp
    refine ⟨⟨ca, da, ?_, ?_, congrArg Prod.fst hp⟩, ⟨cb, db, ?_, ?_, congrArg Prod.snd hp⟩⟩
    · exact (gammaGroundGammaProductCodePieceEquiv_left_val _ _ cs).trans (congrArg gammaCodeLeft hc')
    · exact (gammaGroundGammaProductCodePieceEquiv_left_val _ _ ds).trans (congrArg gammaCodeLeft hd')
    · exact (gammaGroundGammaProductCodePieceEquiv_right_val _ _ cs).trans (congrArg gammaCodeRight hc')
    · exact (gammaGroundGammaProductCodePieceEquiv_right_val _ _ ds).trans (congrArg gammaCodeRight hd')
  · rintro ⟨⟨ca, da, hca, hda, hF⟩, ⟨cb, db, hcb, hdb, hG⟩⟩
    let cs := gammaGroundGammaProductCode (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) ca cb
    let ds := gammaGroundGammaProductCode (A'.piece (finProdFinEquiv.symm j).1) (B'.piece (finProdFinEquiv.symm j).2) da db
    refine ⟨cs, ds, ?_, ?_, ?_⟩
    · change gammaCodeAppend ca.val cb.val = c
      rw [hca, hcb, gammaCodeAppend_left_right]
    · change gammaCodeAppend da.val db.val = d
      rw [hda, hdb, gammaCodeAppend_left_right]
    · apply (A'.productCodeEquiv B').injective
      change A'.productCodeEquiv B' (gammaGroundGammaProductCodeFunctionEquiv F G ⟨i, gammaGroundGammaProductCode _ _ ca cb⟩) =
        A'.productCodeEquiv B' ⟨j, gammaGroundGammaProductCode _ _ da db⟩
      rw [gammaGroundGammaProductCodeFunctionEquiv_factor, GammaGroundGammaObject.productCodeEquiv_code, GammaGroundGammaObject.productCodeEquiv_code]
      exact Prod.ext hF hG

theorem gammaGroundGammaProductCodeFunctionEquiv_definable (F : GammaGroundFamilyBijection A.codeLift A'.codeLift)
    (G : GammaGroundFamilyBijection B.codeLift B'.codeLift) :
    GammaGroundFamilyDefinable (A.product B).codeLift (A'.product B').codeLift (gammaGroundGammaProductCodeFunctionEquiv F G) := by
  intro i j
  have hF := gammaGroundRelationDefinable_pullback (F.definable (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1)
    (gammaGroundGammaCodeLeftMap hc ground k l) (gammaGroundGammaCodeLeftMap hc ground k l)
  have hG := gammaGroundRelationDefinable_pullback (G.definable (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2)
    (gammaGroundGammaCodeRightMap hc ground k l) (gammaGroundGammaCodeRightMap hc ground k l)
  exact (hF.inter hG).congr (fun z => (gammaGroundGammaProductCodeFunctionEquiv_graph F G i j z.1 z.2).symm)

def gammaGroundGammaProductCodeBijection (F : GammaGroundFamilyBijection A.codeLift A'.codeLift)
    (G : GammaGroundFamilyBijection B.codeLift B'.codeLift) :
    GammaGroundFamilyBijection (A.product B).codeLift (A'.product B').codeLift :=
  ⟨gammaGroundGammaProductCodeFunctionEquiv F G, gammaGroundGammaProductCodeFunctionEquiv_definable F G⟩

end DiamondIntegral.Section3
