import «section 3».GammaGroundFiniteGammaPositiveComparison
import «section 3».GammaGroundGammaProducts
import «section 3».GammaGroundGammaGradedSemiring
/-! Actual graded finite Gamma products and the injective graded inclusion into Gamma. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def gammaGroundFiniteGammaRepresentative {k : ℕ} (a : GammaGroundFiniteGammaKPlus (M := M) hc ground k) : GammaGroundFiniteGammaObject hc ground k :=
  Classical.choose (gammaGroundFiniteGammaClass_surjective a)

@[simp] theorem gammaGroundFiniteGammaRepresentative_class {k : ℕ} (a : GammaGroundFiniteGammaKPlus (M := M) hc ground k) :
    gammaGroundFiniteGammaClass (gammaGroundFiniteGammaRepresentative a) = a := Classical.choose_spec (gammaGroundFiniteGammaClass_surjective a)

def gammaGroundFiniteGammaClassMul {k l : ℕ} (a : GammaGroundFiniteGammaKPlus (M := M) hc ground k) (b : GammaGroundFiniteGammaKPlus (M := M) hc ground l) : GammaGroundFiniteGammaKPlus hc ground (k + l) :=
  gammaGroundFiniteGammaClass ((gammaGroundFiniteGammaRepresentative a).product (gammaGroundFiniteGammaRepresentative b))

theorem gammaGroundFiniteGammaToGammaKPlus_mul {k l : ℕ} (a : GammaGroundFiniteGammaKPlus (M := M) hc ground k) (b : GammaGroundFiniteGammaKPlus (M := M) hc ground l) :
    gammaGroundFiniteGammaToGammaKPlus (gammaGroundFiniteGammaClassMul a b) =
      DiamondIntegral.Section3.gammaGroundGammaClassMul (gammaGroundFiniteGammaToGammaKPlus a) (gammaGroundFiniteGammaToGammaKPlus b) := by
  have ha : gammaGroundGammaClass (gammaGroundFiniteGammaRepresentative a).obj = gammaGroundFiniteGammaToGammaKPlus a := by
    rw [← gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundFiniteGammaRepresentative_class]
  have hb : gammaGroundGammaClass (gammaGroundFiniteGammaRepresentative b).obj = gammaGroundFiniteGammaToGammaKPlus b := by
    rw [← gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundFiniteGammaRepresentative_class]
  change gammaGroundFiniteGammaToGammaKPlus (gammaGroundFiniteGammaClass ((gammaGroundFiniteGammaRepresentative a).product (gammaGroundFiniteGammaRepresentative b))) = _
  rw [gammaGroundFiniteGammaToGammaKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.gammaGroundGammaClassMul_class
    (gammaGroundFiniteGammaRepresentative a).obj (gammaGroundFiniteGammaRepresentative b).obj).symm

@[simp] theorem gammaGroundFiniteGammaClassMul_class {k l : ℕ} (U : GammaGroundFiniteGammaObject (M := M) hc ground k) (V : GammaGroundFiniteGammaObject (M := M) hc ground l) :
    gammaGroundFiniteGammaClassMul (gammaGroundFiniteGammaClass U) (gammaGroundFiniteGammaClass V) = gammaGroundFiniteGammaClass (U.product V) := by
  apply gammaGroundFiniteGammaToGammaKPlus_injective
  rw [gammaGroundFiniteGammaToGammaKPlus_mul, gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundFiniteGammaToGammaKPlus_class, gammaGroundFiniteGammaToGammaKPlus_class]
  exact DiamondIntegral.Section3.gammaGroundGammaClassMul_class U.obj V.obj

instance gammaGroundFiniteGammaKPlusGMul : GradedMonoid.GMul (GammaGroundFiniteGammaKPlus (M := M) hc ground) := ⟨gammaGroundFiniteGammaClassMul⟩
instance gammaGroundFiniteGammaKPlusGOne : GradedMonoid.GOne (GammaGroundFiniteGammaKPlus (M := M) hc ground) := ⟨gammaGroundFiniteGammaClass (GammaGroundFiniteGammaObject.unit hc ground)⟩

instance gammaGroundFiniteGammaKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundFiniteGammaKPlus (M := M) hc ground) where
  mul_zero a := by
    change gammaGroundFiniteGammaClassMul a 0 = 0
    apply gammaGroundFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundFiniteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := GammaGroundGammaKPlus hc ground) _
  zero_mul b := by
    change gammaGroundFiniteGammaClassMul 0 b = 0
    apply gammaGroundFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundFiniteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := GammaGroundGammaKPlus hc ground) _
  mul_add a b c := by
    change gammaGroundFiniteGammaClassMul a (b + c) = gammaGroundFiniteGammaClassMul a b + gammaGroundFiniteGammaClassMul a c
    apply gammaGroundFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundFiniteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := GammaGroundGammaKPlus hc ground) _ _ _
  add_mul a b c := by
    change gammaGroundFiniteGammaClassMul (a + b) c = gammaGroundFiniteGammaClassMul a c + gammaGroundFiniteGammaClassMul b c
    apply gammaGroundFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundFiniteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := GammaGroundGammaKPlus hc ground) _ _ _

abbrev GammaGroundFiniteGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundFiniteGammaKPlus (M := M) hc ground)

def gammaGroundFiniteGammaDirectSumToGamma : GammaGroundFiniteGammaDirectSum (M := M) hc ground →+
    DiamondIntegral.Section3.GammaGroundGammaDirectSum (M := M) hc ground :=
  DirectSum.map (fun _ => gammaGroundFiniteGammaToGammaKPlus)

theorem gammaGroundFiniteGammaDirectSumToGamma_injective : Function.Injective (gammaGroundFiniteGammaDirectSumToGamma (M := M) (hc := hc) (ground := ground)) :=
  (DirectSum.map_injective (fun _ => gammaGroundFiniteGammaToGammaKPlus)).mpr (fun _ => gammaGroundFiniteGammaToGammaKPlus_injective)

theorem gammaGroundFiniteGammaDirectSumToGamma_one : gammaGroundFiniteGammaDirectSumToGamma (1 : GammaGroundFiniteGammaDirectSum (M := M) hc ground) = 1 := by
  change DirectSum.map (fun _ => gammaGroundFiniteGammaToGammaKPlus)
    (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) 0 (gammaGroundFiniteGammaClass (GammaGroundFiniteGammaObject.unit hc ground))) =
      DirectSum.of (DiamondIntegral.Section3.GammaGroundGammaKPlus hc ground) 0
        (DiamondIntegral.Section3.gammaGroundGammaClass (GammaGroundGammaObject.unit hc ground))
  rw [DirectSum.map_of, gammaGroundFiniteGammaToGammaKPlus_class]
  rfl

theorem gammaGroundFiniteGammaDirectSumToGamma_mul (a b : GammaGroundFiniteGammaDirectSum (M := M) hc ground) :
    gammaGroundFiniteGammaDirectSumToGamma (a * b) = gammaGroundFiniteGammaDirectSumToGamma a * gammaGroundFiniteGammaDirectSumToGamma b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [gammaGroundFiniteGammaDirectSumToGamma, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.GammaGroundGammaKPlus hc ground) (i + j))
        (gammaGroundFiniteGammaToGammaKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance gammaGroundFiniteGammaDirectSumCommMonoid : CommMonoid (GammaGroundFiniteGammaDirectSum (M := M) hc ground) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply gammaGroundFiniteGammaDirectSumToGamma_injective
    simp only [gammaGroundFiniteGammaDirectSumToGamma_mul, mul_assoc]
  one_mul a := by
    apply gammaGroundFiniteGammaDirectSumToGamma_injective
    simp only [gammaGroundFiniteGammaDirectSumToGamma_mul, gammaGroundFiniteGammaDirectSumToGamma_one, one_mul]
  mul_one a := by
    apply gammaGroundFiniteGammaDirectSumToGamma_injective
    simp only [gammaGroundFiniteGammaDirectSumToGamma_mul, gammaGroundFiniteGammaDirectSumToGamma_one, mul_one]
  mul_comm a b := by
    apply gammaGroundFiniteGammaDirectSumToGamma_injective
    rw [gammaGroundFiniteGammaDirectSumToGamma_mul, gammaGroundFiniteGammaDirectSumToGamma_mul]
    exact mul_comm _ _

instance gammaGroundFiniteGammaDirectSumCommSemiring : CommSemiring (GammaGroundFiniteGammaDirectSum (M := M) hc ground) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : GammaGroundFiniteGammaDirectSum hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def gammaGroundFiniteGammaDirectSumClass {k : ℕ} (U : GammaGroundFiniteGammaObject (M := M) hc ground k) : GammaGroundFiniteGammaDirectSum hc ground :=
  DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass U)

theorem gammaGroundFiniteGammaDirectSumClass_product {k l : ℕ} (U : GammaGroundFiniteGammaObject (M := M) hc ground k) (V : GammaGroundFiniteGammaObject (M := M) hc ground l) :
    gammaGroundFiniteGammaDirectSumClass (U.product V) = gammaGroundFiniteGammaDirectSumClass U * gammaGroundFiniteGammaDirectSumClass V := by
  rw [gammaGroundFiniteGammaDirectSumClass, gammaGroundFiniteGammaDirectSumClass, gammaGroundFiniteGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) (k + l)) (gammaGroundFiniteGammaClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def gammaGroundFiniteGammaGradedInclusion : GammaGroundFiniteGammaDirectSum (M := M) hc ground →+* GammaGroundGammaDirectSum hc ground where
  __ := gammaGroundFiniteGammaDirectSumToGamma
  map_one' := gammaGroundFiniteGammaDirectSumToGamma_one
  map_mul' := gammaGroundFiniteGammaDirectSumToGamma_mul

theorem gammaGroundFiniteGammaGradedInclusion_injective :
    Function.Injective (gammaGroundFiniteGammaGradedInclusion (M := M) (hc := hc) (ground := ground)) := gammaGroundFiniteGammaDirectSumToGamma_injective

end DiamondIntegral.Section3
