import «section 3».GammaGroundRESPositiveComparison
import «section 3».GammaGroundRVGradedSemiring

/-! Actual graded RES products and the injective graded inclusion into RV. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def GammaGroundRESObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) : GammaGroundRESObject hc ground 0 :=
  ⟨GammaGroundRVObject.unit hc ground, (GammaGroundRVObject.unit hc ground).degree_zero_res⟩

def gammaGroundRESRepresentative {k : ℕ} (a : GammaGroundRESKPlus hc ground k) : GammaGroundRESObject hc ground k :=
  Classical.choose (gammaGroundRESClass_surjective a)

@[simp] theorem gammaGroundRESRepresentative_class {k : ℕ} (a : GammaGroundRESKPlus hc ground k) :
    gammaGroundRESClass (gammaGroundRESRepresentative a) = a := Classical.choose_spec (gammaGroundRESClass_surjective a)

def gammaGroundRESClassMul {k l : ℕ} (a : GammaGroundRESKPlus hc ground k) (b : GammaGroundRESKPlus hc ground l) : GammaGroundRESKPlus hc ground (k + l) :=
  gammaGroundRESClass ((gammaGroundRESRepresentative a).product (gammaGroundRESRepresentative b))

theorem gammaGroundRESToRVKPlus_mul {k l : ℕ} (a : GammaGroundRESKPlus hc ground k) (b : GammaGroundRESKPlus hc ground l) :
    gammaGroundRESToRVKPlus (gammaGroundRESClassMul a b) =
      DiamondIntegral.Section3.gammaGroundRVClassMul (gammaGroundRESToRVKPlus a) (gammaGroundRESToRVKPlus b) := by
  have ha : gammaGroundRVClass (gammaGroundRESRepresentative a).obj = gammaGroundRESToRVKPlus a := by
    rw [← gammaGroundRESToRVKPlus_class, gammaGroundRESRepresentative_class]
  have hb : gammaGroundRVClass (gammaGroundRESRepresentative b).obj = gammaGroundRESToRVKPlus b := by
    rw [← gammaGroundRESToRVKPlus_class, gammaGroundRESRepresentative_class]
  change gammaGroundRESToRVKPlus (gammaGroundRESClass ((gammaGroundRESRepresentative a).product (gammaGroundRESRepresentative b))) = _
  rw [gammaGroundRESToRVKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.gammaGroundRVClassMul_class
    (gammaGroundRESRepresentative a).obj (gammaGroundRESRepresentative b).obj).symm

@[simp] theorem gammaGroundRESClassMul_class {k l : ℕ} (U : GammaGroundRESObject hc ground k) (V : GammaGroundRESObject hc ground l) :
    gammaGroundRESClassMul (gammaGroundRESClass U) (gammaGroundRESClass V) = gammaGroundRESClass (U.product V) := by
  apply gammaGroundRESToRVKPlus_injective
  rw [gammaGroundRESToRVKPlus_mul, gammaGroundRESToRVKPlus_class, gammaGroundRESToRVKPlus_class, gammaGroundRESToRVKPlus_class]
  exact DiamondIntegral.Section3.gammaGroundRVClassMul_class U.obj V.obj

instance gammaGroundRESKPlusGMul : GradedMonoid.GMul (GammaGroundRESKPlus hc ground) := ⟨gammaGroundRESClassMul⟩
instance gammaGroundRESKPlusGOne : GradedMonoid.GOne (GammaGroundRESKPlus hc ground) := ⟨gammaGroundRESClass (GammaGroundRESObject.unit hc ground)⟩

instance gammaGroundRESKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundRESKPlus hc ground) where
  mul_zero a := by
    change gammaGroundRESClassMul a 0 = 0
    apply gammaGroundRESToRVKPlus_injective
    simp only [gammaGroundRESToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := GammaGroundRVKPlus hc ground) _
  zero_mul b := by
    change gammaGroundRESClassMul 0 b = 0
    apply gammaGroundRESToRVKPlus_injective
    simp only [gammaGroundRESToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := GammaGroundRVKPlus hc ground) _
  mul_add a b c := by
    change gammaGroundRESClassMul a (b + c) = gammaGroundRESClassMul a b + gammaGroundRESClassMul a c
    apply gammaGroundRESToRVKPlus_injective
    simp only [gammaGroundRESToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := GammaGroundRVKPlus hc ground) _ _ _
  add_mul a b c := by
    change gammaGroundRESClassMul (a + b) c = gammaGroundRESClassMul a c + gammaGroundRESClassMul b c
    apply gammaGroundRESToRVKPlus_injective
    simp only [gammaGroundRESToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := GammaGroundRVKPlus hc ground) _ _ _

abbrev GammaGroundRESDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundRESKPlus hc ground)

def gammaGroundRESDirectSumToRV : GammaGroundRESDirectSum hc ground →+
    DiamondIntegral.Section3.GammaGroundRVDirectSum hc ground :=
  DirectSum.map (fun _ => gammaGroundRESToRVKPlus)

theorem gammaGroundRESDirectSumToRV_injective : Function.Injective (gammaGroundRESDirectSumToRV (M := M) (hc := hc) (ground := ground)) :=
  (DirectSum.map_injective (fun _ => gammaGroundRESToRVKPlus)).mpr (fun _ => gammaGroundRESToRVKPlus_injective)

theorem gammaGroundRESDirectSumToRV_one : gammaGroundRESDirectSumToRV (1 : GammaGroundRESDirectSum hc ground) = 1 := by
  change DirectSum.map (fun _ => gammaGroundRESToRVKPlus)
    (DirectSum.of (GammaGroundRESKPlus hc ground) 0 (gammaGroundRESClass (GammaGroundRESObject.unit hc ground))) =
      DirectSum.of (DiamondIntegral.Section3.GammaGroundRVKPlus hc ground) 0
        (DiamondIntegral.Section3.gammaGroundRVClass (GammaGroundRVObject.unit hc ground))
  rw [DirectSum.map_of, gammaGroundRESToRVKPlus_class]
  rfl

theorem gammaGroundRESDirectSumToRV_mul (a b : GammaGroundRESDirectSum hc ground) :
    gammaGroundRESDirectSumToRV (a * b) = gammaGroundRESDirectSumToRV a * gammaGroundRESDirectSumToRV b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [gammaGroundRESDirectSumToRV, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.GammaGroundRVKPlus hc ground) (i + j))
        (gammaGroundRESToRVKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance gammaGroundRESDirectSumCommMonoid : CommMonoid (GammaGroundRESDirectSum hc ground) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply gammaGroundRESDirectSumToRV_injective
    simp only [gammaGroundRESDirectSumToRV_mul, mul_assoc]
  one_mul a := by
    apply gammaGroundRESDirectSumToRV_injective
    simp only [gammaGroundRESDirectSumToRV_mul, gammaGroundRESDirectSumToRV_one, one_mul]
  mul_one a := by
    apply gammaGroundRESDirectSumToRV_injective
    simp only [gammaGroundRESDirectSumToRV_mul, gammaGroundRESDirectSumToRV_one, mul_one]
  mul_comm a b := by
    apply gammaGroundRESDirectSumToRV_injective
    simp only [gammaGroundRESDirectSumToRV_mul, mul_comm]

instance gammaGroundRESDirectSumCommSemiring : CommSemiring (GammaGroundRESDirectSum hc ground) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : GammaGroundRESDirectSum hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def gammaGroundRESDirectSumClass {k : ℕ} (U : GammaGroundRESObject hc ground k) : GammaGroundRESDirectSum hc ground :=
  DirectSum.of (GammaGroundRESKPlus hc ground) k (gammaGroundRESClass U)

theorem gammaGroundRESDirectSumClass_product {k l : ℕ} (U : GammaGroundRESObject hc ground k) (V : GammaGroundRESObject hc ground l) :
    gammaGroundRESDirectSumClass (U.product V) = gammaGroundRESDirectSumClass U * gammaGroundRESDirectSumClass V := by
  rw [gammaGroundRESDirectSumClass, gammaGroundRESDirectSumClass, gammaGroundRESDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundRESKPlus hc ground) (k + l)) (gammaGroundRESClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundRESGradedInclusion : GammaGroundRESDirectSum hc ground →+* GammaGroundRVDirectSum hc ground where
  __ := gammaGroundRESDirectSumToRV
  map_one' := gammaGroundRESDirectSumToRV_one
  map_mul' := gammaGroundRESDirectSumToRV_mul

theorem gammaGroundRESGradedInclusion_injective :
    Function.Injective (gammaGroundRESGradedInclusion (M := M) (hc := hc) (ground := ground)) := gammaGroundRESDirectSumToRV_injective

end DiamondIntegral.Section3
