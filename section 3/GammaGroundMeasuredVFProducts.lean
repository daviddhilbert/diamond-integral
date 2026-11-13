import «section 3».GammaGroundMeasuredVFData
import «section 3».GammaGroundMixedProducts

/-! Measured VF cartesian products retain both forms and finite RV
fibres over the complete Gamma ground, uniformly in degree zero. -/
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

def gammaGroundMeasuredVFProductLeft (U : GammaGroundMeasuredVFData hc ground k)
    (V : GammaGroundMeasuredVFData hc ground l) : GammaGroundMap (gammaGroundMixedProductDomain U.domain V.domain) U.domain :=
  (GammaGroundMap.prodFst U.domain V.domain).comp (gammaGroundMixedUnpack U.domain V.domain)

def gammaGroundMeasuredVFProductRight (U : GammaGroundMeasuredVFData hc ground k)
    (V : GammaGroundMeasuredVFData hc ground l) : GammaGroundMap (gammaGroundMixedProductDomain U.domain V.domain) V.domain :=
  (GammaGroundMap.prodSnd U.domain V.domain).comp (gammaGroundMixedUnpack U.domain V.domain)

def GammaGroundMeasuredVFData.product (U : GammaGroundMeasuredVFData hc ground k)
    (V : GammaGroundMeasuredVFData hc ground l) : GammaGroundMeasuredVFData hc ground (k + l) where
  arity := U.arity + V.arity
  domain := gammaGroundMixedProductDomain U.domain V.domain
  finite := gammaGroundMixedProduct_finite U.finite V.finite
  form := GammaGroundVolumeForm.mul (U.form.comp (gammaGroundMeasuredVFProductLeft U V))
    (V.form.comp (gammaGroundMeasuredVFProductRight U V))

@[simp] theorem GammaGroundMeasuredVFData.product_form (U : GammaGroundMeasuredVFData hc ground k)
    (V : GammaGroundMeasuredVFData hc ground l) (a : (U.product V).domain) :
    gammaGroundFormValue (U.product V).form a =
      gammaGroundFormValue U.form (gammaGroundMeasuredVFProductLeft U V a) *
        gammaGroundFormValue V.form (gammaGroundMeasuredVFProductRight U V a) := rfl

end DiamondIntegral.Section3
