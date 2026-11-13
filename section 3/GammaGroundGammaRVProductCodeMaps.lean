import «section 3».GammaGroundGammaRVProductLift
import «section 3».GammaGroundMeasuredGammaRVLift
import «section 3».GammaGroundGammaProductCodeMaps
/-! Product lift maps on every full Gamma code. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

theorem gammaGroundGammaRVProductBijection_code (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (i : Fin (A.tags * B.tags))
    (a : gammaGroundCodePreimage (A.piece (finProdFinEquiv.symm i).1))
    (b : gammaGroundCodePreimage (B.piece (finProdFinEquiv.symm i).2)) :
    (gammaGroundGammaRVProductBijection A B).map ((A.product B).rvEncodeCode
      ⟨i, gammaGroundGammaProductCode _ _ a b⟩) =
      gammaGroundRVPackPair A.rvLift.domain B.rvLift.domain
        (A.rvEncodeCode ⟨(finProdFinEquiv.symm i).1, a⟩)
        (B.rvEncodeCode ⟨(finProdFinEquiv.symm i).2, b⟩) := by
  change gammaGroundRVFamilyProductMap A.rvPieces B.rvPieces
    (gammaGroundRVFamilyMap (gammaGroundGammaRVProductFamilies A B).equiv (gammaGroundGammaRVProductFamilies A B).definable
      ((A.product B).rvPieces.rvEncode _)) = _
  rw [gammaGroundRVFamilyMap_encode]
  have he : (gammaGroundGammaRVProductFamilies A B).equiv
      ((A.product B).rvCodeBijection.equiv ⟨i, gammaGroundGammaProductCode _ _ a b⟩) =
      (⟨i, gammaGroundRVPackPair _ _ ((gammaGroundGammaRVCodeBijection _).map a)
        ((gammaGroundGammaRVCodeBijection _).map b)⟩ : (A.rvPieces.rvProduct B.rvPieces).Carrier) := by
    apply congrArg (fun p : (A.rvPieces.rvProduct B.rvPieces).piece i =>
      (⟨i, p⟩ : (A.rvPieces.rvProduct B.rvPieces).Carrier))
    apply Subtype.ext
    exact gammaCodeAppend_tuple a.val b.val
  rw [he]
  change gammaGroundRVFamilyDesc (A.rvPieces.rvProduct B.rvPieces) _ _ _ = _
  rw [gammaGroundRVFamilyDesc_encode, gammaGroundRVFamilyProductBranch_pair]
  rfl

end DiamondIntegral.Section3
