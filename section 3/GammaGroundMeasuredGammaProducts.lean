import «section 3».GammaGroundGammaProducts
import «section 3».GammaGroundVolumeForms
import «section 3».GammaGroundGammaVolumeCategories
/-! Measured Gamma products retain their full forms, including on finite
domains. The coordinate concatenation is a genuine definable bijection. -/

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

def gammaGroundGammaProductLeft (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    GammaGroundMap (gammaGroundGammaAppendMap A B).image A :=
  (GammaGroundMap.prodFst A B).comp (gammaGroundGammaAppendBijection A B).symm.map

def gammaGroundGammaProductRight (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    GammaGroundMap (gammaGroundGammaAppendMap A B).image B :=
  (GammaGroundMap.prodSnd A B).comp (gammaGroundGammaAppendBijection A B).symm.map

@[reducible] def GammaGroundMeasuredGammaObject.product (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l) :
    GammaGroundMeasuredGammaObject hc ground (k + l) where
  underlying := A.underlying.product B.underlying
  form i :=
    let a := (finProdFinEquiv.symm i).1
    let b := (finProdFinEquiv.symm i).2
    GammaGroundVolumeForm.mul ((A.form a).comp (gammaGroundGammaProductLeft (A.underlying.piece a) (B.underlying.piece b)))
      ((B.form b).comp (gammaGroundGammaProductRight (A.underlying.piece a) (B.underlying.piece b)))

def GammaGroundMeasuredGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    GammaGroundMeasuredGammaObject hc ground 0 := ⟨GammaGroundGammaObject.unit hc ground, fun i => gammaGroundOneForm _⟩

def GammaGroundMeasuredFiniteGammaObject.product (A : GammaGroundMeasuredFiniteGammaObject hc ground k)
    (B : GammaGroundMeasuredFiniteGammaObject hc ground l) : GammaGroundMeasuredFiniteGammaObject hc ground (k + l) :=
  ⟨A.obj.product B.obj, A.obj.underlying.product_finite B.obj.underlying A.property B.property⟩

def GammaGroundMeasuredFiniteGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    GammaGroundMeasuredFiniteGammaObject hc ground 0 :=
  ⟨GammaGroundMeasuredGammaObject.unit hc ground, (GammaGroundGammaObject.unit hc ground).degree_zero_finite⟩

end DiamondIntegral.Section3
