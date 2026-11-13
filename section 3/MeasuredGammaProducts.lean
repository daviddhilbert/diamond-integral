import «section 3».GammaProducts
import «section 3».GammaFormOperations

/-! Measured Gamma products retain their full forms, including on finite
domains. The coordinate concatenation is a genuine definable bijection. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaProductLeft (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    Map (gammaAppendMap A B).image A :=
  (Map.prodFst A B).comp (gammaAppendBijection A B).symm.map

def gammaProductRight (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    Map (gammaAppendMap A B).image B :=
  (Map.prodSnd A B).comp (gammaAppendBijection A B).symm.map

@[reducible] def MeasuredGammaObject.product (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l) :
    MeasuredGammaObject hc S (k + l) where
  underlying := A.underlying.product B.underlying
  form i :=
    let a := (finProdFinEquiv.symm i).1
    let b := (finProdFinEquiv.symm i).2
    GammaVolumeForm.mul ((A.form a).comp (gammaProductLeft (A.underlying.piece a) (B.underlying.piece b)))
      ((B.form b).comp (gammaProductRight (A.underlying.piece a) (B.underlying.piece b)))

def MeasuredGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    MeasuredGammaObject hc S 0 := ⟨GammaObject.unit hc S, fun i => gammaOneForm hc _⟩

def MeasuredFiniteGammaObject.product (A : MeasuredFiniteGammaObject hc S k)
    (B : MeasuredFiniteGammaObject hc S l) : MeasuredFiniteGammaObject hc S (k + l) :=
  ⟨A.obj.product B.obj, A.obj.underlying.product_finite B.obj.underlying A.property B.property⟩

def MeasuredFiniteGammaObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    MeasuredFiniteGammaObject hc S 0 :=
  ⟨MeasuredGammaObject.unit hc S, (GammaObject.unit hc S).degree_zero_finite⟩

end DiamondIntegral.Section3
