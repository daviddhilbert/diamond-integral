import «section 3».GammaGroundGammaCodeMapCategory
import «section 3».GammaGroundGammaCodeProjections
import «section 3».GammaGroundFamilyTagMaps
import «section 3».GammaGroundFamilyPartitions
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaProductLeftCodePieceMap (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (i : Fin (A.tags * B.tags)) :
    GammaGroundMap ((A.product B).codeLift.piece i) (A.codeLift.piece (finProdFinEquiv.symm i).1) :=
  ((gammaGroundGammaCodeLeftMap hc ground k l).comp (GammaGroundMap.inclusion (fun _ _ => Set.mem_univ _))).corestrict (by
    intro c
    change gammaCodeLeft c.val ∈ (A.codeLift.piece (finProdFinEquiv.symm i).1).carrier
    rw [← gammaGroundGammaProductCodePieceEquiv_left_val
      (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) c]
    exact (gammaGroundGammaProductCodePieceEquiv _ _ c).1.property)

def gammaGroundGammaProductRightCodePieceMap (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (i : Fin (A.tags * B.tags)) :
    GammaGroundMap ((A.product B).codeLift.piece i) (B.codeLift.piece (finProdFinEquiv.symm i).2) :=
  ((gammaGroundGammaCodeRightMap hc ground k l).comp (GammaGroundMap.inclusion (fun _ _ => Set.mem_univ _))).corestrict (by
    intro c
    change gammaCodeRight c.val ∈ (B.codeLift.piece (finProdFinEquiv.symm i).2).carrier
    rw [← gammaGroundGammaProductCodePieceEquiv_right_val
      (A.piece (finProdFinEquiv.symm i).1) (B.piece (finProdFinEquiv.symm i).2) c]
    exact (gammaGroundGammaProductCodePieceEquiv _ _ c).2.property)

def gammaGroundGammaProductLeftCodeFamilyMap (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    GammaGroundFamilyMap (A.product B).codeLift A.codeLift where
  toFun c := (A.productCodeEquiv B c).1
  definable := (gammaGroundFamilyTaggedMap_definable (A.product B).codeLift A.codeLift
    (fun i => (finProdFinEquiv.symm i).1) (gammaGroundGammaProductLeftCodePieceMap A B)).congr_fun (by
      intro c
      apply gammaGroundFamilyCarrier_ext A.codeLift
      · rfl
      · exact (gammaGroundGammaProductCodePieceEquiv_left_val _ _ c.2).symm)

def gammaGroundGammaProductRightCodeFamilyMap (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    GammaGroundFamilyMap (A.product B).codeLift B.codeLift where
  toFun c := (A.productCodeEquiv B c).2
  definable := (gammaGroundFamilyTaggedMap_definable (A.product B).codeLift B.codeLift
    (fun i => (finProdFinEquiv.symm i).2) (gammaGroundGammaProductRightCodePieceMap A B)).congr_fun (by
      intro c
      apply gammaGroundFamilyCarrier_ext B.codeLift
      · rfl
      · exact (gammaGroundGammaProductCodePieceEquiv_right_val _ _ c.2).symm)

def gammaGroundGammaCodeProductFst (A B : GammaGroundGammaCodeObject hc ground) : A.product B ⟶ A where
  map := gammaGroundGammaProductLeftCodeFamilyMap A.obj B.obj
  respects c d h := by
    have ht := (A.obj.productCodeEquiv_decode B.obj c).symm.trans
      ((congrArg (A.obj.productCarrierEquiv B.obj) h).trans (A.obj.productCodeEquiv_decode B.obj d))
    exact congrArg Prod.fst ht

def gammaGroundGammaCodeProductSnd (A B : GammaGroundGammaCodeObject hc ground) : A.product B ⟶ B where
  map := gammaGroundGammaProductRightCodeFamilyMap A.obj B.obj
  respects c d h := by
    have ht := (A.obj.productCodeEquiv_decode B.obj c).symm.trans
      ((congrArg (A.obj.productCarrierEquiv B.obj) h).trans (A.obj.productCodeEquiv_decode B.obj d))
    exact congrArg Prod.snd ht

end DiamondIntegral.Section3
