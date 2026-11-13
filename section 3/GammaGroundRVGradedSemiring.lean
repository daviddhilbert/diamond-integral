import «section 3».GammaGroundRVProductDistributivity
import Mathlib.Algebra.DirectSum.Ring

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance gammaGroundRVKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundRVKPlus hc ground) where
  mul_zero := gammaGroundRVClassMul_zero
  zero_mul := gammaGroundRVClassMul_zero_left
  mul_add := gammaGroundRVClassMul_add
  add_mul := gammaGroundRVClassMul_add_left

instance gammaGroundRVKPlusGSemiring : DirectSum.GSemiring (GammaGroundRVKPlus hc ground) where
  natCast n := n • gammaGroundRVClass (GammaGroundRVObject.unit hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance gammaGroundRVKPlusGCommSemiring : DirectSum.GCommSemiring (GammaGroundRVKPlus hc ground) where

/-- Finite sums of the genuine positive RV scissors in all degrees,
with multiplication induced by the actual cartesian RV product. -/
abbrev GammaGroundRVDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundRVKPlus hc ground)

def gammaGroundRVDirectSumClass {k : ℕ} (U : GammaGroundRVObject hc ground k) : GammaGroundRVDirectSum hc ground :=
  DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass U)

theorem gammaGroundRVDirectSumClass_product {k l : ℕ} (U : GammaGroundRVObject hc ground k)
    (V : GammaGroundRVObject hc ground l) :
    gammaGroundRVDirectSumClass (U.product V) = gammaGroundRVDirectSumClass U * gammaGroundRVDirectSumClass V := by
  rw [gammaGroundRVDirectSumClass, gammaGroundRVDirectSumClass, gammaGroundRVDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundRVKPlus hc ground) (k + l)) (gammaGroundRVClassMul_class U V).symm

theorem gammaGroundRVDirectSumClass_coprod {k : ℕ} (U V : GammaGroundRVObject hc ground k) :
    gammaGroundRVDirectSumClass (U.coprod V) = gammaGroundRVDirectSumClass U + gammaGroundRVDirectSumClass V := by
  change DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass (U.coprod V)) = _
  rw [gammaGroundRVClass_coprod, map_add]
  rfl

theorem gammaGroundRVDirectSumClass_unit : gammaGroundRVDirectSumClass (GammaGroundRVObject.unit hc ground) = 1 := rfl

end DiamondIntegral.Section3

end
