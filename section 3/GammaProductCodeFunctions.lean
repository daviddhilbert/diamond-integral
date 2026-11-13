import «section 3».GammaCodeProjections

/-! Products of arbitrary definable full-code family bijections remain
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}
variable {A A' : GammaObject hc S k} {B B' : GammaObject hc S l}

def gammaProductCodeFunctionEquiv (F : FamilyBijection A.codeLift A'.codeLift)
    (G : FamilyBijection B.codeLift B'.codeLift) :
    (A.product B).codeLift.Carrier ≃ (A'.product B').codeLift.Carrier :=
  (A.productCodeEquiv B).trans ((Equiv.prodCongr F.equiv G.equiv).trans (A'.productCodeEquiv B').symm)

theorem gammaProductCodeFunctionEquiv_factor (F : FamilyBijection A.codeLift A'.codeLift)
    (G : FamilyBijection B.codeLift B'.codeLift) (c : (A.product B).codeLift.Carrier) :
    A'.productCodeEquiv B' (gammaProductCodeFunctionEquiv F G c) =
      (F.equiv (A.productCodeEquiv B c).1, G.equiv (A.productCodeEquiv B c).2) :=
  (A'.productCodeEquiv B').apply_symm_apply _

theorem gammaProductCodeFunctionEquiv_graph (F : FamilyBijection A.codeLift A'.codeLift)
    (G : FamilyBijection B.codeLift B'.codeLift) (i : Fin (A.tags * B.tags)) (j : Fin (A'.tags * B'.tags))
    (c d : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    familyGraph (A.product B).codeLift (A'.product B').codeLift (gammaProductCodeFunctionEquiv F G) i j c d ↔
      familyGraph A.codeLift A'.codeLift F.equiv (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
        (gammaCodeLeft c) (gammaCodeLeft d) ∧
      familyGraph B.codeLift B'.codeLift G.equiv (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
        (gammaCodeRight c) (gammaCodeRight d) := by
  constructor
  · rintro ⟨cs, ds, hc', hd', he⟩
    let ca := (gammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) cs).1
    let cb := (gammaProductCodePieceEquiv (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) cs).2
    let da := (gammaProductCodePieceEquiv (A'.piece (finProdFinEquiv.symm j).1) (B'.piece (finProdFinEquiv.symm j).2) ds).1
    let db := (gammaProductCodePieceEquiv (A'.piece (finProdFinEquiv.symm j).1) (B'.piece (finProdFinEquiv.symm j).2) ds).2
    have hp := (gammaProductCodeFunctionEquiv_factor F G ⟨i, cs⟩).symm.trans
      (congrArg (A'.productCodeEquiv B') he)
    change (F.equiv ⟨(finProdFinEquiv.symm i).1, ca⟩, G.equiv ⟨(finProdFinEquiv.symm i).2, cb⟩) =
      (⟨(finProdFinEquiv.symm j).1, da⟩, ⟨(finProdFinEquiv.symm j).2, db⟩) at hp
    refine ⟨⟨ca, da, ?_, ?_, congrArg Prod.fst hp⟩, ⟨cb, db, ?_, ?_, congrArg Prod.snd hp⟩⟩
    · exact (gammaProductCodePieceEquiv_left_val _ _ cs).trans (congrArg gammaCodeLeft hc')
    · exact (gammaProductCodePieceEquiv_left_val _ _ ds).trans (congrArg gammaCodeLeft hd')
    · exact (gammaProductCodePieceEquiv_right_val _ _ cs).trans (congrArg gammaCodeRight hc')
    · exact (gammaProductCodePieceEquiv_right_val _ _ ds).trans (congrArg gammaCodeRight hd')
  · rintro ⟨⟨ca, da, hca, hda, hF⟩, ⟨cb, db, hcb, hdb, hG⟩⟩
    let cs := gammaProductCode (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) ca cb
    let ds := gammaProductCode (A'.piece (finProdFinEquiv.symm j).1) (B'.piece (finProdFinEquiv.symm j).2) da db
    refine ⟨cs, ds, ?_, ?_, ?_⟩
    · change gammaCodeAppend ca.val cb.val = c
      rw [hca, hcb, gammaCodeAppend_left_right]
    · change gammaCodeAppend da.val db.val = d
      rw [hda, hdb, gammaCodeAppend_left_right]
    · apply (A'.productCodeEquiv B').injective
      change A'.productCodeEquiv B' (gammaProductCodeFunctionEquiv F G ⟨i, gammaProductCode _ _ ca cb⟩) =
        A'.productCodeEquiv B' ⟨j, gammaProductCode _ _ da db⟩
      rw [gammaProductCodeFunctionEquiv_factor, GammaObject.productCodeEquiv_code, GammaObject.productCodeEquiv_code]
      exact Prod.ext hF hG

theorem gammaProductCodeFunctionEquiv_definable (F : FamilyBijection A.codeLift A'.codeLift)
    (G : FamilyBijection B.codeLift B'.codeLift) :
    FamilyDefinable (A.product B).codeLift (A'.product B').codeLift (gammaProductCodeFunctionEquiv F G) := by
  intro i j
  have hF := relationDefinable_pullback (F.definable (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1)
    (gammaCodeLeftMap hc S k l) (gammaCodeLeftMap hc S k l)
  have hG := relationDefinable_pullback (G.definable (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2)
    (gammaCodeRightMap hc S k l) (gammaCodeRightMap hc S k l)
  exact (hF.inter _ _ hG).congr _ _ (fun c d => (gammaProductCodeFunctionEquiv_graph F G i j c d).symm)

def gammaProductCodeBijection (F : FamilyBijection A.codeLift A'.codeLift)
    (G : FamilyBijection B.codeLift B'.codeLift) :
    FamilyBijection (A.product B).codeLift (A'.product B').codeLift :=
  ⟨gammaProductCodeFunctionEquiv F G, gammaProductCodeFunctionEquiv_definable F G⟩

end DiamondIntegral.Section3
