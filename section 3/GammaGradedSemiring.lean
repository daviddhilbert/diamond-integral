import «section 3».GammaHomogeneousProducts
import Mathlib.Algebra.DirectSum.Ring

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

open SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance gammaKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (GammaKPlus (M := M) hc S) where
  mul_zero := gammaClassMul_zero
  zero_mul := gammaClassMul_zero_left
  mul_add := gammaClassMul_add
  add_mul := gammaClassMul_add_left

instance gammaKPlusGSemiring : DirectSum.GSemiring (GammaKPlus (M := M) hc S) where
  natCast n := n • gammaClass (GammaObject.unit hc S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance gammaKPlusGCommSemiring : DirectSum.GCommSemiring (GammaKPlus (M := M) hc S) where

/-- Finite sums of the genuine positive Gamma scissors in all degrees,
with multiplication induced by the actual cartesian Gamma product. -/
abbrev GammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) := DirectSum ℕ (GammaKPlus (M := M) hc S)

def gammaDirectSumClass (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (U : GammaObject (M := M) hc S k) : GammaDirectSum (M := M) hc S :=
  DirectSum.of (GammaKPlus hc S) k (gammaClass U)

theorem gammaDirectSumClass_product {k l : ℕ} (U : GammaObject (M := M) hc S k)
    (V : GammaObject (M := M) hc S l) :
    gammaDirectSumClass hc (U.product V) = gammaDirectSumClass hc U * gammaDirectSumClass hc V := by
  rw [gammaDirectSumClass, gammaDirectSumClass, gammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaKPlus hc S) (k + l)) (gammaClassMul_class U V).symm

theorem gammaDirectSumClass_coprod {k : ℕ} (U V : GammaObject (M := M) hc S k) :
    gammaDirectSumClass hc (U.coprod V) = gammaDirectSumClass hc U + gammaDirectSumClass hc V := by
  change DirectSum.of (GammaKPlus hc S) k (gammaClass (U.coprod V)) = _
  rw [gammaClass_coprod, map_add]
  rfl

theorem gammaDirectSumClass_unit : gammaDirectSumClass hc (GammaObject.unit (M := M) hc S) = 1 := rfl

end DiamondIntegral.Section3

end
