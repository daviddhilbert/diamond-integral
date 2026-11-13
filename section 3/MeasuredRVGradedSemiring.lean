import «section 3».MeasuredRVHomogeneousProducts
import Mathlib.Algebra.DirectSum.Ring

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

open SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance measuredRVKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (MeasuredRVKPlus (M := M) hc S) where
  mul_zero := measuredRVClassMul_zero
  zero_mul := measuredRVClassMul_zero_left
  mul_add := measuredRVClassMul_add
  add_mul := measuredRVClassMul_add_left

instance measuredRVKPlusGSemiring : DirectSum.GSemiring (MeasuredRVKPlus (M := M) hc S) where
  natCast n := n • measuredRVClass hc (MeasuredRVObject.unit hc S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance measuredRVKPlusGCommSemiring : DirectSum.GCommSemiring (MeasuredRVKPlus (M := M) hc S) where

/-- Finite sums of the genuine positive RV scissors in all degrees,
with multiplication induced by the actual cartesian RV product. -/
abbrev MeasuredRVDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) := DirectSum ℕ (MeasuredRVKPlus (M := M) hc S)

def measuredRVDirectSumClass (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (U : MeasuredRVObject (M := M) S k) : MeasuredRVDirectSum (M := M) hc S :=
  DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc U)

theorem measuredRVDirectSumClass_product {k l : ℕ} (U : MeasuredRVObject (M := M) S k)
    (V : MeasuredRVObject (M := M) S l) :
    measuredRVDirectSumClass hc (U.product hc V) = measuredRVDirectSumClass hc U * measuredRVDirectSumClass hc V := by
  rw [measuredRVDirectSumClass, measuredRVDirectSumClass, measuredRVDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (MeasuredRVKPlus hc S) (k + l)) (measuredRVClassMul_class U V).symm

theorem measuredRVDirectSumClass_coprod {k : ℕ} (U V : MeasuredRVObject (M := M) S k) :
    measuredRVDirectSumClass hc (U.coprod hc V) = measuredRVDirectSumClass hc U + measuredRVDirectSumClass hc V := by
  change DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc (U.coprod hc V)) = _
  rw [measuredRVClass_coprod hc, map_add]
  rfl

theorem measuredRVDirectSumClass_unit : measuredRVDirectSumClass hc (MeasuredRVObject.unit (M := M) hc S) = 1 := rfl

end DiamondIntegral.Section3

end
