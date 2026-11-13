import «section 3».GammaGroundRVProductCoordinates
import «section 3».GammaGroundMeasuredRVProducts

/-! Actual product arrows preserve the full combined Gamma weight. -/
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

def gammaGroundMeasuredRVProductHom {U U' : GammaGroundMeasuredRVObject hc ground k}
    {V V' : GammaGroundMeasuredRVObject hc ground l}
    (f : GammaGroundMeasuredRVHom U U') (g : GammaGroundMeasuredRVHom V V') :
    GammaGroundMeasuredRVHom (U.product V) (U'.product V') where
  bijection := gammaGroundRVProductBijection f.bijection g.bijection
  preserves a := by
    rw [GammaGroundMeasuredRVObject.product_combined, GammaGroundMeasuredRVObject.product_combined]
    have he := gammaGroundRVProductBijection_unpack f.bijection g.bijection a
    have hl : gammaGroundMeasuredRVProductLeft U' V'
        ((gammaGroundRVProductBijection f.bijection g.bijection).map a) =
        f.bijection.map (gammaGroundMeasuredRVProductLeft U V a) := by
      apply Subtype.ext
      exact congrArg (fun z : U'.underlying.domain.prod V'.underlying.domain => z.val.1) he
    have hr : gammaGroundMeasuredRVProductRight U' V'
        ((gammaGroundRVProductBijection f.bijection g.bijection).map a) =
        g.bijection.map (gammaGroundMeasuredRVProductRight U V a) := by
      apply Subtype.ext
      exact congrArg (fun z : U'.underlying.domain.prod V'.underlying.domain => z.val.2) he
    rw [hl, hr, ← f.preserves, ← g.preserves]

def gammaGroundMeasuredRVProductIso {U U' : GammaGroundMeasuredRVObject hc ground k}
    {V V' : GammaGroundMeasuredRVObject hc ground l} (f : U ≅ U') (g : V ≅ V') :
    U.product V ≅ U'.product V' := asIso (show _ ⟶ _ from gammaGroundMeasuredRVProductHom f.hom g.hom)

end DiamondIntegral.Section3
