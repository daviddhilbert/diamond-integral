import «section 3».MeasuredGammaProductLift
import «section 3».GammaProductMorphisms

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

theorem measuredGammaProduct_factor (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l)
    (p : (A.underlying.product B.underlying).Carrier) :
    (A.product B).combinedWeight p =
      A.combinedWeight (A.underlying.productCarrierEquiv B.underlying p).1 *
        B.combinedWeight (A.underlying.productCarrierEquiv B.underlying p).2 := by
  obtain ⟨⟨i, c⟩, rfl⟩ := (A.underlying.product B.underlying).decode_surjective p
  obtain ⟨a, b, rfl⟩ := gammaProductCode_surjective
    (A.underlying.piece (finProdFinEquiv.symm i).1)
    (B.underlying.piece (finProdFinEquiv.symm i).2) c
  rw [GammaObject.productCodeEquiv_decode, GammaObject.productCodeEquiv_code]
  exact measuredGammaProduct_combined_code A B i a b

theorem measuredGammaProduct_preserves {A A' : MeasuredGammaObject hc S k} {B B' : MeasuredGammaObject hc S l}
    (f : MeasuredGammaHom A A') (g : MeasuredGammaHom B B')
    (p : (A.underlying.product B.underlying).Carrier) :
    (A.product B).combinedWeight p = (A'.product B').combinedWeight
      ((f.underlying.product g.underlying).bijection.equiv p) := by
  have hs := measuredGammaProduct_factor A B p
  have ht := measuredGammaProduct_factor A' B' ((f.underlying.product g.underlying).bijection.equiv p)
  have hf := f.underlying.product_factor g.underlying p
  rw [hf] at ht
  exact hs.trans ((congrArg₂ (· * ·) (f.preserves _) (g.preserves _)).trans ht.symm)

def MeasuredGammaHom.product {A A' : MeasuredGammaObject hc S k} {B B' : MeasuredGammaObject hc S l}
    (f : MeasuredGammaHom A A') (g : MeasuredGammaHom B B') :
    MeasuredGammaHom (A.product B) (A'.product B') where
  underlying := f.underlying.product g.underlying
  preserves := measuredGammaProduct_preserves f g

end DiamondIntegral.Section3
