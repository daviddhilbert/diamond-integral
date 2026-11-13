import «section 3».MeasuredGammaHomogeneousProducts
import Mathlib.Algebra.DirectSum.Ring

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

open SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance measuredGammaKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (MeasuredGammaKPlus (M := M) hc S) where
  mul_zero := measuredGammaClassMul_zero
  zero_mul := measuredGammaClassMul_zero_left
  mul_add := measuredGammaClassMul_add
  add_mul := measuredGammaClassMul_add_left

instance measuredGammaKPlusGSemiring : DirectSum.GSemiring (MeasuredGammaKPlus (M := M) hc S) where
  natCast n := n • measuredGammaClass (MeasuredGammaObject.unit hc S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance measuredGammaKPlusGCommSemiring : DirectSum.GCommSemiring (MeasuredGammaKPlus (M := M) hc S) where

/-- Finite sums of the genuine positive Gamma scissors in all degrees,
with multiplication induced by the actual cartesian Gamma product. -/
abbrev MeasuredGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) := DirectSum ℕ (MeasuredGammaKPlus (M := M) hc S)

def measuredGammaDirectSumClass (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (U : MeasuredGammaObject (M := M) hc S k) : MeasuredGammaDirectSum (M := M) hc S :=
  DirectSum.of (MeasuredGammaKPlus hc S) k (measuredGammaClass U)

theorem measuredGammaDirectSumClass_product {k l : ℕ} (U : MeasuredGammaObject (M := M) hc S k)
    (V : MeasuredGammaObject (M := M) hc S l) :
    measuredGammaDirectSumClass hc (U.product V) = measuredGammaDirectSumClass hc U * measuredGammaDirectSumClass hc V := by
  rw [measuredGammaDirectSumClass, measuredGammaDirectSumClass, measuredGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (MeasuredGammaKPlus hc S) (k + l)) (measuredGammaClassMul_class U V).symm

theorem measuredGammaDirectSumClass_coprod {k : ℕ} (U V : MeasuredGammaObject (M := M) hc S k) :
    measuredGammaDirectSumClass hc (U.coprod V) = measuredGammaDirectSumClass hc U + measuredGammaDirectSumClass hc V := by
  change DirectSum.of (MeasuredGammaKPlus hc S) k (measuredGammaClass (U.coprod V)) = _
  rw [measuredGammaClass_coprod, map_add]
  rfl

theorem measuredGammaDirectSumClass_unit : measuredGammaDirectSumClass hc (MeasuredGammaObject.unit (M := M) hc S) = 1 := rfl

end DiamondIntegral.Section3

end
