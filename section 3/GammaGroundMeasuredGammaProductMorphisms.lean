import «section 3».GammaGroundMeasuredGammaProductWeights
import «section 3».GammaGroundGammaProductMorphisms
/-! Actual measured Gamma product arrows preserve combined weights
through the canonical decomposition into the two original factors. -/
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

theorem gammaGroundMeasuredGammaProduct_factor (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l)
    (p : (A.underlying.product B.underlying).Carrier) :
    (A.product B).combinedWeight p =
      A.combinedWeight (A.underlying.productCarrierEquiv B.underlying p).1 *
        B.combinedWeight (A.underlying.productCarrierEquiv B.underlying p).2 := by
  obtain ⟨⟨i, c⟩, rfl⟩ := (A.underlying.product B.underlying).decode_surjective p
  obtain ⟨a, b, rfl⟩ := gammaGroundGammaProductCode_surjective
    (A.underlying.piece (finProdFinEquiv.symm i).1)
    (B.underlying.piece (finProdFinEquiv.symm i).2) c
  rw [GammaGroundGammaObject.productCodeEquiv_decode, GammaGroundGammaObject.productCodeEquiv_code]
  exact gammaGroundMeasuredGammaProduct_combined_code A B i a b

theorem gammaGroundMeasuredGammaProduct_preserves {A A' : GammaGroundMeasuredGammaObject hc ground k} {B B' : GammaGroundMeasuredGammaObject hc ground l}
    (f : GammaGroundMeasuredGammaHom A A') (g : GammaGroundMeasuredGammaHom B B')
    (p : (A.underlying.product B.underlying).Carrier) :
    (A.product B).combinedWeight p = (A'.product B').combinedWeight
      ((f.underlying.product g.underlying).bijection.equiv p) := by
  have hs := gammaGroundMeasuredGammaProduct_factor A B p
  have ht := gammaGroundMeasuredGammaProduct_factor A' B' ((f.underlying.product g.underlying).bijection.equiv p)
  have hf := f.underlying.product_factor g.underlying p
  rw [hf] at ht
  exact hs.trans ((congrArg₂ (· * ·) (f.preserves _) (g.preserves _)).trans ht.symm)

def GammaGroundMeasuredGammaHom.product {A A' : GammaGroundMeasuredGammaObject hc ground k} {B B' : GammaGroundMeasuredGammaObject hc ground l}
    (f : GammaGroundMeasuredGammaHom A A') (g : GammaGroundMeasuredGammaHom B B') :
    GammaGroundMeasuredGammaHom (A.product B) (A'.product B') where
  underlying := f.underlying.product g.underlying
  preserves := gammaGroundMeasuredGammaProduct_preserves f g

end DiamondIntegral.Section3
