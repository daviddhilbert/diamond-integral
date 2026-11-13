import «section 3».GammaGroundUnaryAffineContractions
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The unary criterion applies to the paper's full code-preimage
contraction witnesses, without requiring that the RV map be bijective. -/
theorem gammaGroundUnary_code_contraction_piecewiseIntegralAffine [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 2 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (I J : GammaGroundGammaPiece hc B 1) (h : GammaGroundMap I J)
    (F : GammaGroundMap (gammaGroundCodePreimage I) (gammaGroundCodePreimage J))
    (hF : ∀ c, gammaGroundCodeDecode J (F c) = h (gammaGroundCodeDecode I c)) :
    GammaGroundUnaryPiecewiseIntegralAffine h := by
  let a := gammaGroundRVUnitFullCodeBijection I
  let b := gammaGroundRVUnitFullCodeBijection J
  let f := b.symm.map.comp (F.comp a.map)
  apply gammaGroundUnary_contraction_piecewiseIntegralAffine hκ hs h00 hsmall hγsmall RY I J h f
  intro u
  have hd := gammaGroundRVUnitFullCode_inverse_decode J (F (a.map u))
  have he := congrArg Subtype.val (hF (a.map u))
  have hi : gammaGroundCodeDecode I (a.map u) = gammaGroundFullPreimageValueMap I u :=
    Subtype.ext (gammaGroundRVUnitFullCode_decode I u)
  exact hd.symm.trans (he.trans (congrArg (fun γ : I => (h γ).val) hi))

/-- Both sentences of Remark 3.15 now have their actual full-ground
context: the unary contraction has integer slopes and genuine RV shifts. -/
theorem gammaGroundContext_unary_contraction_piecewiseIntegralAffine
    (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (RY : GammaGroundCoefficientClassification C)
    (I J : GammaGroundGammaPiece hc C.base 1) (h : GammaGroundMap I J)
    (F : GammaGroundMap (gammaGroundCodePreimage I) (gammaGroundCodePreimage J))
    (hF : ∀ c, gammaGroundCodeDecode J (F c) = h (gammaGroundCodeDecode I c)) :
    GammaGroundUnaryPiecewiseIntegralAffine h := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero C.model00
  exact gammaGroundUnary_code_contraction_piecewiseIntegralAffine C.uncountable C.saturated C.model00
    C.small_real C.small_gamma (RY 2) I J h F hF

end DiamondIntegral.Section3
