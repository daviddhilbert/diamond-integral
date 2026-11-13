import «section 3».GammaGroundIntegralAffineContractions
import «section 3».GammaGroundCoefficientMonicityContext
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- The arbitrary-tuple criterion applies to the paper's full code-preimage
contraction witnesses, without requiring that the RV map be bijective. -/
theorem gammaGround_code_contraction_piecewiseIntegralAffine [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin (n+m) → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (I : GammaGroundGammaPiece hc B n) (J : GammaGroundGammaPiece hc B m) (h : GammaGroundMap I J)
    (F : GammaGroundMap (gammaGroundCodePreimage I) (gammaGroundCodePreimage J))
    (hF : ∀ c, gammaGroundCodeDecode J (F c) = h (gammaGroundCodeDecode I c)) :
    GammaGroundPiecewiseIntegralAffine h := by
  let a := gammaGroundRVUnitFullCodeBijection I
  let b := gammaGroundRVUnitFullCodeBijection J
  let f := b.symm.map.comp (F.comp a.map)
  apply gammaGround_contraction_piecewiseIntegralAffine hκ hs h00 hsmall hγsmall RY I J h f
  intro u
  have hd := gammaGroundRVUnitFullCode_inverse_decode J (F (a.map u))
  have he := congrArg Subtype.val (hF (a.map u))
  have hi : gammaGroundCodeDecode I (a.map u) = gammaGroundFullPreimageValueMap I u :=
    Subtype.ext (gammaGroundRVUnitFullCode_decode I u)
  exact hd.symm.trans (he.trans (congrArg (fun γ : I => (h γ).val) hi))

/-- Both sentences of Remark 3.15 now have their actual full-ground
context: all contractions have rectangular integer matrices and genuine RV shifts. -/
theorem gammaGroundContext_contraction_piecewiseIntegralAffine
    (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (RY : GammaGroundCoefficientClassification C)
    (I : GammaGroundGammaPiece hc C.base n) (J : GammaGroundGammaPiece hc C.base m) (h : GammaGroundMap I J)
    (F : GammaGroundMap (gammaGroundCodePreimage I) (gammaGroundCodePreimage J))
    (hF : ∀ c, gammaGroundCodeDecode J (F c) = h (gammaGroundCodeDecode I c)) :
    GammaGroundPiecewiseIntegralAffine h := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero C.model00
  exact gammaGround_code_contraction_piecewiseIntegralAffine C.uncountable C.saturated C.model00
    C.small_real C.small_gamma (RY (n+m)) I J h F hF

end DiamondIntegral.Section3
