import «section 3».GammaCodeMapCategory
import «section 3».GammaCodeProjections
import «section 3».FamilyTagMaps
import «section 3».FamilyPartitions

/-! The full-code Gamma product has actual definable projections that
respect the imaginary decoding relation. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaProductLeftCodePieceMap (A : GammaObject hc S k) (B : GammaObject hc S l)
    (i : Fin (A.tags * B.tags)) :
    Map ((A.product B).codeLift.piece i) (A.codeLift.piece (finProdFinEquiv.symm i).1) :=
  ((gammaCodeLeftMap hc S k l).comp (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict (by
    intro c
    change gammaCodeLeft c.val ∈ (A.codeLift.piece (finProdFinEquiv.symm i).1).carrier
    rw [← gammaProductCodePieceEquiv_left_val
      (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) c]
    exact (gammaProductCodePieceEquiv _ _ c).1.property)

def gammaProductRightCodePieceMap (A : GammaObject hc S k) (B : GammaObject hc S l)
    (i : Fin (A.tags * B.tags)) :
    Map ((A.product B).codeLift.piece i) (B.codeLift.piece (finProdFinEquiv.symm i).2) :=
  ((gammaCodeRightMap hc S k l).comp (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict (by
    intro c
    change gammaCodeRight c.val ∈ (B.codeLift.piece (finProdFinEquiv.symm i).2).carrier
    rw [← gammaProductCodePieceEquiv_right_val
      (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) c]
    exact (gammaProductCodePieceEquiv _ _ c).2.property)

def gammaProductLeftCodeFamilyMap (A : GammaObject hc S k) (B : GammaObject hc S l) :
    FamilyMap (A.product B).codeLift A.codeLift where
  toFun c := (A.productCodeEquiv B c).1
  definable := (familyTaggedMap_definable (A.product B).codeLift A.codeLift
    (fun i => (finProdFinEquiv.symm i).1) (gammaProductLeftCodePieceMap A B)).congr_fun (by
      intro c
      apply familyCarrier_ext A.codeLift
      · rfl
      · exact (gammaProductCodePieceEquiv_left_val _ _ c.2).symm)

def gammaProductRightCodeFamilyMap (A : GammaObject hc S k) (B : GammaObject hc S l) :
    FamilyMap (A.product B).codeLift B.codeLift where
  toFun c := (A.productCodeEquiv B c).2
  definable := (familyTaggedMap_definable (A.product B).codeLift B.codeLift
    (fun i => (finProdFinEquiv.symm i).2) (gammaProductRightCodePieceMap A B)).congr_fun (by
      intro c
      apply familyCarrier_ext B.codeLift
      · rfl
      · exact (gammaProductCodePieceEquiv_right_val _ _ c.2).symm)

def gammaCodeProductFst (A B : GammaCodeObject hc S) : A.product B ⟶ A where
  map := gammaProductLeftCodeFamilyMap A.obj B.obj
  respects c d h := by
    have ht := (A.obj.productCodeEquiv_decode B.obj c).symm.trans
      ((congrArg (A.obj.productCarrierEquiv B.obj) h).trans (A.obj.productCodeEquiv_decode B.obj d))
    exact congrArg Prod.fst ht

def gammaCodeProductSnd (A B : GammaCodeObject hc S) : A.product B ⟶ B where
  map := gammaProductRightCodeFamilyMap A.obj B.obj
  respects c d h := by
    have ht := (A.obj.productCodeEquiv_decode B.obj c).symm.trans
      ((congrArg (A.obj.productCarrierEquiv B.obj) h).trans (A.obj.productCodeEquiv_decode B.obj d))
    exact congrArg Prod.snd ht

end DiamondIntegral.Section3
