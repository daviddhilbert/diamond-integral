import Mathlib.Algebra.DirectSum.Ring
import «section 3».GammaGroundGammaHomogeneousProducts
set_option autoImplicit false
noncomputable section

namespace DiamondIntegral.Section3
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

instance gammaGroundGammaKPlusGNonUnitalNonAssocSemiring : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundGammaKPlus (M := M) hc ground) where
  mul_zero := gammaGroundGammaClassMul_zero
  zero_mul := gammaGroundGammaClassMul_zero_left
  mul_add := gammaGroundGammaClassMul_add
  add_mul := gammaGroundGammaClassMul_add_left

instance gammaGroundGammaKPlusGSemiring : DirectSum.GSemiring (GammaGroundGammaKPlus (M := M) hc ground) where
  natCast n := n • gammaGroundGammaClass (GammaGroundGammaObject.unit hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul, one_nsmul]
    rfl

instance gammaGroundGammaKPlusGCommSemiring : DirectSum.GCommSemiring (GammaGroundGammaKPlus (M := M) hc ground) where

/-- Finite sums of the genuine positive Gamma scissors in all degrees,
with multiplication induced by the actual cartesian Gamma product. -/
abbrev GammaGroundGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundGammaKPlus (M := M) hc ground)

def gammaGroundGammaDirectSumClass (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (U : GammaGroundGammaObject (M := M) hc ground k) : GammaGroundGammaDirectSum (M := M) hc ground :=
  DirectSum.of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass U)

theorem gammaGroundGammaDirectSumClass_product {k l : ℕ} (U : GammaGroundGammaObject (M := M) hc ground k)
    (V : GammaGroundGammaObject (M := M) hc ground l) :
    gammaGroundGammaDirectSumClass hc (U.product V) = gammaGroundGammaDirectSumClass hc U * gammaGroundGammaDirectSumClass hc V := by
  rw [gammaGroundGammaDirectSumClass, gammaGroundGammaDirectSumClass, gammaGroundGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundGammaKPlus hc ground) (k + l)) (gammaGroundGammaClassMul_class U V).symm

theorem gammaGroundGammaDirectSumClass_coprod {k : ℕ} (U V : GammaGroundGammaObject (M := M) hc ground k) :
    gammaGroundGammaDirectSumClass hc (U.coprod V) = gammaGroundGammaDirectSumClass hc U + gammaGroundGammaDirectSumClass hc V := by
  change DirectSum.of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass (U.coprod V)) = _
  rw [gammaGroundGammaClass_coprod, map_add]
  rfl

theorem gammaGroundGammaDirectSumClass_unit : gammaGroundGammaDirectSumClass hc (GammaGroundGammaObject.unit (M := M) hc ground) = 1 := rfl

end DiamondIntegral.Section3

end
