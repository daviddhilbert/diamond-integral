import «section 3».GammaGroundMeasuredRESPositiveComparison
import «section 3».GammaGroundMeasuredRESProducts
import «section 3».GammaGroundMeasuredRVGradedSemiring

/-! Actual graded RES products and the injective graded inclusion into RV. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def GammaGroundMeasuredRESObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) : GammaGroundMeasuredRESObject hc ground 0 :=
  ⟨GammaGroundMeasuredRVObject.unit hc ground, (GammaGroundMeasuredRVObject.unit hc ground).underlying.degree_zero_res⟩

def gammaGroundMeasuredRESRepresentative {k : ℕ} (a : GammaGroundMeasuredRESKPlus hc ground k) : GammaGroundMeasuredRESObject hc ground k :=
  Classical.choose (gammaGroundMeasuredRESClass_surjective a)

@[simp] theorem gammaGroundMeasuredRESRepresentative_class {k : ℕ} (a : GammaGroundMeasuredRESKPlus hc ground k) :
    gammaGroundMeasuredRESClass (gammaGroundMeasuredRESRepresentative a) = a := Classical.choose_spec (gammaGroundMeasuredRESClass_surjective a)

def gammaGroundMeasuredRESClassMul {k l : ℕ} (a : GammaGroundMeasuredRESKPlus hc ground k) (b : GammaGroundMeasuredRESKPlus hc ground l) : GammaGroundMeasuredRESKPlus hc ground (k + l) :=
  gammaGroundMeasuredRESClass ((gammaGroundMeasuredRESRepresentative a).product (gammaGroundMeasuredRESRepresentative b))

theorem gammaGroundMeasuredRESToRVKPlus_mul {k l : ℕ} (a : GammaGroundMeasuredRESKPlus hc ground k) (b : GammaGroundMeasuredRESKPlus hc ground l) :
    gammaGroundMeasuredRESToRVKPlus (gammaGroundMeasuredRESClassMul a b) =
      DiamondIntegral.Section3.gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRESToRVKPlus a) (gammaGroundMeasuredRESToRVKPlus b) := by
  have ha : gammaGroundMeasuredRVClass (gammaGroundMeasuredRESRepresentative a).obj = gammaGroundMeasuredRESToRVKPlus a := by
    rw [← gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESRepresentative_class]
  have hb : gammaGroundMeasuredRVClass (gammaGroundMeasuredRESRepresentative b).obj = gammaGroundMeasuredRESToRVKPlus b := by
    rw [← gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESRepresentative_class]
  change gammaGroundMeasuredRESToRVKPlus (gammaGroundMeasuredRESClass ((gammaGroundMeasuredRESRepresentative a).product (gammaGroundMeasuredRESRepresentative b))) = _
  rw [gammaGroundMeasuredRESToRVKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.gammaGroundMeasuredRVClassMul_class
    (gammaGroundMeasuredRESRepresentative a).obj (gammaGroundMeasuredRESRepresentative b).obj).symm

@[simp] theorem gammaGroundMeasuredRESClassMul_class {k l : ℕ} (U : GammaGroundMeasuredRESObject hc ground k) (V : GammaGroundMeasuredRESObject hc ground l) :
    gammaGroundMeasuredRESClassMul (gammaGroundMeasuredRESClass U) (gammaGroundMeasuredRESClass V) = gammaGroundMeasuredRESClass (U.product V) := by
  apply gammaGroundMeasuredRESToRVKPlus_injective
  rw [gammaGroundMeasuredRESToRVKPlus_mul, gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESToRVKPlus_class, gammaGroundMeasuredRESToRVKPlus_class]
  exact DiamondIntegral.Section3.gammaGroundMeasuredRVClassMul_class U.obj V.obj

instance gammaGroundMeasuredRESKPlusGMul : GradedMonoid.GMul (GammaGroundMeasuredRESKPlus hc ground) := ⟨gammaGroundMeasuredRESClassMul⟩
instance gammaGroundMeasuredRESKPlusGOne : GradedMonoid.GOne (GammaGroundMeasuredRESKPlus hc ground) := ⟨gammaGroundMeasuredRESClass (GammaGroundMeasuredRESObject.unit hc ground)⟩

instance gammaGroundMeasuredRESKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundMeasuredRESKPlus hc ground) where
  mul_zero a := by
    change gammaGroundMeasuredRESClassMul a 0 = 0
    apply gammaGroundMeasuredRESToRVKPlus_injective
    simp only [gammaGroundMeasuredRESToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := GammaGroundMeasuredRVKPlus hc ground) _
  zero_mul b := by
    change gammaGroundMeasuredRESClassMul 0 b = 0
    apply gammaGroundMeasuredRESToRVKPlus_injective
    simp only [gammaGroundMeasuredRESToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := GammaGroundMeasuredRVKPlus hc ground) _
  mul_add a b c := by
    change gammaGroundMeasuredRESClassMul a (b + c) = gammaGroundMeasuredRESClassMul a b + gammaGroundMeasuredRESClassMul a c
    apply gammaGroundMeasuredRESToRVKPlus_injective
    simp only [gammaGroundMeasuredRESToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := GammaGroundMeasuredRVKPlus hc ground) _ _ _
  add_mul a b c := by
    change gammaGroundMeasuredRESClassMul (a + b) c = gammaGroundMeasuredRESClassMul a c + gammaGroundMeasuredRESClassMul b c
    apply gammaGroundMeasuredRESToRVKPlus_injective
    simp only [gammaGroundMeasuredRESToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := GammaGroundMeasuredRVKPlus hc ground) _ _ _

abbrev GammaGroundMeasuredRESDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundMeasuredRESKPlus hc ground)

def gammaGroundMeasuredRESDirectSumToRV : GammaGroundMeasuredRESDirectSum hc ground →+
    DiamondIntegral.Section3.GammaGroundMeasuredRVDirectSum hc ground :=
  DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)

theorem gammaGroundMeasuredRESDirectSumToRV_injective : Function.Injective (gammaGroundMeasuredRESDirectSumToRV (M := M) (hc := hc) (ground := ground)) :=
  (DirectSum.map_injective (fun _ => gammaGroundMeasuredRESToRVKPlus)).mpr (fun _ => gammaGroundMeasuredRESToRVKPlus_injective)

theorem gammaGroundMeasuredRESDirectSumToRV_one : gammaGroundMeasuredRESDirectSumToRV (1 : GammaGroundMeasuredRESDirectSum hc ground) = 1 := by
  change DirectSum.map (fun _ => gammaGroundMeasuredRESToRVKPlus)
    (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) 0 (gammaGroundMeasuredRESClass (GammaGroundMeasuredRESObject.unit hc ground))) =
      DirectSum.of (DiamondIntegral.Section3.GammaGroundMeasuredRVKPlus hc ground) 0
        (DiamondIntegral.Section3.gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.unit hc ground))
  rw [DirectSum.map_of, gammaGroundMeasuredRESToRVKPlus_class]
  rfl

theorem gammaGroundMeasuredRESDirectSumToRV_mul (a b : GammaGroundMeasuredRESDirectSum hc ground) :
    gammaGroundMeasuredRESDirectSumToRV (a * b) = gammaGroundMeasuredRESDirectSumToRV a * gammaGroundMeasuredRESDirectSumToRV b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [gammaGroundMeasuredRESDirectSumToRV, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.GammaGroundMeasuredRVKPlus hc ground) (i + j))
        (gammaGroundMeasuredRESToRVKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance gammaGroundMeasuredRESDirectSumCommMonoid : CommMonoid (GammaGroundMeasuredRESDirectSum hc ground) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    simp only [gammaGroundMeasuredRESDirectSumToRV_mul, mul_assoc]
  one_mul a := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    simp only [gammaGroundMeasuredRESDirectSumToRV_mul, gammaGroundMeasuredRESDirectSumToRV_one, one_mul]
  mul_one a := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    simp only [gammaGroundMeasuredRESDirectSumToRV_mul, gammaGroundMeasuredRESDirectSumToRV_one, mul_one]
  mul_comm a b := by
    apply gammaGroundMeasuredRESDirectSumToRV_injective
    simp only [gammaGroundMeasuredRESDirectSumToRV_mul, mul_comm]

instance gammaGroundMeasuredRESDirectSumCommSemiring : CommSemiring (GammaGroundMeasuredRESDirectSum hc ground) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : GammaGroundMeasuredRESDirectSum hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def gammaGroundMeasuredRESDirectSumClass {k : ℕ} (U : GammaGroundMeasuredRESObject hc ground k) : GammaGroundMeasuredRESDirectSum hc ground :=
  DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) k (gammaGroundMeasuredRESClass U)

theorem gammaGroundMeasuredRESDirectSumClass_product {k l : ℕ} (U : GammaGroundMeasuredRESObject hc ground k) (V : GammaGroundMeasuredRESObject hc ground l) :
    gammaGroundMeasuredRESDirectSumClass (U.product V) = gammaGroundMeasuredRESDirectSumClass U * gammaGroundMeasuredRESDirectSumClass V := by
  rw [gammaGroundMeasuredRESDirectSumClass, gammaGroundMeasuredRESDirectSumClass, gammaGroundMeasuredRESDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc ground) (k + l)) (gammaGroundMeasuredRESClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundMeasuredRESGradedInclusion : GammaGroundMeasuredRESDirectSum hc ground →+* GammaGroundMeasuredRVDirectSum hc ground where
  __ := gammaGroundMeasuredRESDirectSumToRV
  map_one' := gammaGroundMeasuredRESDirectSumToRV_one
  map_mul' := gammaGroundMeasuredRESDirectSumToRV_mul

theorem gammaGroundMeasuredRESGradedInclusion_injective :
    Function.Injective (gammaGroundMeasuredRESGradedInclusion (M := M) (hc := hc) (ground := ground)) := gammaGroundMeasuredRESDirectSumToRV_injective

end DiamondIntegral.Section3
