import Mathlib.Algebra.DirectSum.Ring
import «section 3».GammaGroundMeasuredGammaHomogeneousProducts
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance gammaGroundMeasuredGammaKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundMeasuredGammaKPlus (M := M) hc ground) where
  mul_zero := gammaGroundMeasuredGammaClassMul_zero
  zero_mul := gammaGroundMeasuredGammaClassMul_zero_left
  mul_add := gammaGroundMeasuredGammaClassMul_add
  add_mul := gammaGroundMeasuredGammaClassMul_add_left

instance gammaGroundMeasuredGammaKPlusGSemiring : DirectSum.GSemiring (GammaGroundMeasuredGammaKPlus (M := M) hc ground) where
  natCast n := n • gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.unit hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance gammaGroundMeasuredGammaKPlusGCommSemiring : DirectSum.GCommSemiring (GammaGroundMeasuredGammaKPlus (M := M) hc ground) where

/-- Finite sums of the genuine positive Gamma scissors in all degrees,
with multiplication induced by the actual cartesian Gamma product. -/
abbrev GammaGroundMeasuredGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundMeasuredGammaKPlus (M := M) hc ground)

def gammaGroundMeasuredGammaDirectSumClass (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (U : GammaGroundMeasuredGammaObject (M := M) hc ground k) : GammaGroundMeasuredGammaDirectSum (M := M) hc ground :=
  DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass U)

theorem gammaGroundMeasuredGammaDirectSumClass_product {k l : ℕ} (U : GammaGroundMeasuredGammaObject (M := M) hc ground k)
    (V : GammaGroundMeasuredGammaObject (M := M) hc ground l) :
    gammaGroundMeasuredGammaDirectSumClass hc (U.product V) = gammaGroundMeasuredGammaDirectSumClass hc U * gammaGroundMeasuredGammaDirectSumClass hc V := by
  rw [gammaGroundMeasuredGammaDirectSumClass, gammaGroundMeasuredGammaDirectSumClass, gammaGroundMeasuredGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) (k + l)) (gammaGroundMeasuredGammaClassMul_class U V).symm

theorem gammaGroundMeasuredGammaDirectSumClass_coprod {k : ℕ} (U V : GammaGroundMeasuredGammaObject (M := M) hc ground k) :
    gammaGroundMeasuredGammaDirectSumClass hc (U.coprod V) = gammaGroundMeasuredGammaDirectSumClass hc U + gammaGroundMeasuredGammaDirectSumClass hc V := by
  change DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass (U.coprod V)) = _
  rw [gammaGroundMeasuredGammaClass_coprod, map_add]
  rfl

theorem gammaGroundMeasuredGammaDirectSumClass_unit : gammaGroundMeasuredGammaDirectSumClass hc (GammaGroundMeasuredGammaObject.unit (M := M) hc ground) = 1 := rfl

end DiamondIntegral.Section3

end
