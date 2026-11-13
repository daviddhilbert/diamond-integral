import «section 3».GammaGroundMeasuredRVProductDistributivity
import Mathlib.Algebra.DirectSum.Ring

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance gammaGroundMeasuredRVKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundMeasuredRVKPlus hc ground) where
  mul_zero := gammaGroundMeasuredRVClassMul_zero
  zero_mul := gammaGroundMeasuredRVClassMul_zero_left
  mul_add := gammaGroundMeasuredRVClassMul_add
  add_mul := gammaGroundMeasuredRVClassMul_add_left

instance gammaGroundMeasuredRVKPlusGSemiring : DirectSum.GSemiring (GammaGroundMeasuredRVKPlus hc ground) where
  natCast n := n • gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.unit hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance gammaGroundMeasuredRVKPlusGCommSemiring : DirectSum.GCommSemiring (GammaGroundMeasuredRVKPlus hc ground) where

/-- Finite sums of the genuine positive RV scissors in all degrees,
with multiplication induced by the actual cartesian RV product. -/
abbrev GammaGroundMeasuredRVDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundMeasuredRVKPlus hc ground)

def gammaGroundMeasuredRVDirectSumClass {k : ℕ} (U : GammaGroundMeasuredRVObject hc ground k) : GammaGroundMeasuredRVDirectSum hc ground :=
  DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass U)

theorem gammaGroundMeasuredRVDirectSumClass_product {k l : ℕ} (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) :
    gammaGroundMeasuredRVDirectSumClass (U.product V) = gammaGroundMeasuredRVDirectSumClass U * gammaGroundMeasuredRVDirectSumClass V := by
  rw [gammaGroundMeasuredRVDirectSumClass, gammaGroundMeasuredRVDirectSumClass, gammaGroundMeasuredRVDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) (k + l)) (gammaGroundMeasuredRVClassMul_class U V).symm

theorem gammaGroundMeasuredRVDirectSumClass_coprod {k : ℕ} (U V : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVDirectSumClass (U.coprod V) = gammaGroundMeasuredRVDirectSumClass U + gammaGroundMeasuredRVDirectSumClass V := by
  change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass (U.coprod V)) = _
  rw [gammaGroundMeasuredRVClass_coprod, map_add]
  rfl

theorem gammaGroundMeasuredRVDirectSumClass_unit : gammaGroundMeasuredRVDirectSumClass (GammaGroundMeasuredRVObject.unit hc ground) = 1 := rfl

end DiamondIntegral.Section3

end
