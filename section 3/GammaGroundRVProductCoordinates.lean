import «section 3».GammaGroundRVProductMorphisms

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {k l : ℕ}

theorem gammaGroundRVProductBijection_unpack {U U' : GammaGroundRVObject hc ground k}
    {V V' : GammaGroundRVObject hc ground l} (f : GammaGroundBijection U.domain U'.domain)
    (g : GammaGroundBijection V.domain V'.domain) (a : (U.product V).domain) :
    gammaGroundRVUnpack U'.domain V'.domain ((gammaGroundRVProductBijection f g).map a) =
      (f.map.prodMap g.map) (gammaGroundRVUnpack U.domain V.domain a) := by
  change (gammaGroundRVPack U'.domain V'.domain).toImage.inverse _
    ((gammaGroundRVPack U'.domain V'.domain).toImage
      ((f.map.prodMap g.map) (gammaGroundRVUnpack U.domain V.domain a))) = _
  exact GammaGroundMap.inverse_apply _ _ _

end DiamondIntegral.Section3
