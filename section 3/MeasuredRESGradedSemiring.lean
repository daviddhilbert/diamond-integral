import «section 3».MeasuredRESPositiveComparison
import «section 3».MeasuredRESSemiring
import «section 3».MeasuredRVGradedSemiring

/-! Actual graded RES products and the injective graded inclusion into RV. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredResRepresentative {k : ℕ} (a : MeasuredRESKPlus (M := M) hc S k) : MeasuredRESObject S k :=
  Classical.choose (measuredResClass_surjective hc a)

@[simp] theorem measuredResRepresentative_class {k : ℕ} (a : MeasuredRESKPlus (M := M) hc S k) :
    measuredResClass hc (measuredResRepresentative a) = a := Classical.choose_spec (measuredResClass_surjective hc a)

def measuredResClassMul {k l : ℕ} (a : MeasuredRESKPlus (M := M) hc S k) (b : MeasuredRESKPlus (M := M) hc S l) : MeasuredRESKPlus hc S (k + l) :=
  measuredResClass hc ((measuredResRepresentative a).product hc (measuredResRepresentative b))

theorem measuredResToRVKPlus_mul {k l : ℕ} (a : MeasuredRESKPlus (M := M) hc S k) (b : MeasuredRESKPlus (M := M) hc S l) :
    measuredResToRVKPlus hc (measuredResClassMul a b) =
      measuredRVClassMul (measuredResToRVKPlus hc a) (measuredResToRVKPlus hc b) := by
  have ha : measuredRVClass hc (measuredResRepresentative a).obj = measuredResToRVKPlus hc a := by
    rw [← measuredResToRVKPlus_class hc, measuredResRepresentative_class]
  have hb : measuredRVClass hc (measuredResRepresentative b).obj = measuredResToRVKPlus hc b := by
    rw [← measuredResToRVKPlus_class hc, measuredResRepresentative_class]
  change measuredResToRVKPlus hc (measuredResClass hc ((measuredResRepresentative a).product hc (measuredResRepresentative b))) = _
  rw [measuredResToRVKPlus_class hc, ← ha, ← hb]
  exact (measuredRVClassMul_class
    (measuredResRepresentative a).obj (measuredResRepresentative b).obj).symm

@[simp] theorem measuredResClassMul_class {k l : ℕ} (U : MeasuredRESObject (M := M) S k) (V : MeasuredRESObject (M := M) S l) :
    measuredResClassMul (measuredResClass hc U) (measuredResClass hc V) = measuredResClass hc (U.product hc V) := by
  apply measuredResToRVKPlus_injective hc
  rw [measuredResToRVKPlus_mul, measuredResToRVKPlus_class hc, measuredResToRVKPlus_class hc, measuredResToRVKPlus_class hc]
  exact measuredRVClassMul_class (hc := hc) U.obj V.obj

instance measuredResKPlusGMul : GradedMonoid.GMul (MeasuredRESKPlus (M := M) hc S) := ⟨measuredResClassMul⟩
instance measuredResKPlusGOne : GradedMonoid.GOne (MeasuredRESKPlus (M := M) hc S) := ⟨measuredResClass hc (MeasuredRESObject.unit hc S)⟩

instance measuredResKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (MeasuredRESKPlus (M := M) hc S) where
  mul_zero a := by
    change measuredResClassMul a 0 = 0
    apply measuredResToRVKPlus_injective hc
    simp only [measuredResToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := MeasuredRVKPlus hc S) _
  zero_mul b := by
    change measuredResClassMul 0 b = 0
    apply measuredResToRVKPlus_injective hc
    simp only [measuredResToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := MeasuredRVKPlus hc S) _
  mul_add a b c := by
    change measuredResClassMul a (b + c) = measuredResClassMul a b + measuredResClassMul a c
    apply measuredResToRVKPlus_injective hc
    simp only [measuredResToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := MeasuredRVKPlus hc S) _ _ _
  add_mul a b c := by
    change measuredResClassMul (a + b) c = measuredResClassMul a c + measuredResClassMul b c
    apply measuredResToRVKPlus_injective hc
    simp only [measuredResToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := MeasuredRVKPlus hc S) _ _ _

abbrev MeasuredRESDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) := DirectSum ℕ (MeasuredRESKPlus (M := M) hc S)

def measuredResDirectSumToRV : MeasuredRESDirectSum (M := M) hc S →+
    MeasuredRVDirectSum (M := M) hc S :=
  DirectSum.map (fun _ => measuredResToRVKPlus hc)

theorem measuredResDirectSumToRV_injective : Function.Injective (measuredResDirectSumToRV (M := M) (S := S) (hc := hc)) :=
  (DirectSum.map_injective (fun _ => measuredResToRVKPlus hc)).mpr (fun _ => measuredResToRVKPlus_injective hc)

theorem measuredResDirectSumToRV_one : measuredResDirectSumToRV (1 : MeasuredRESDirectSum (M := M) hc S) = 1 := by
  change DirectSum.map (fun _ => measuredResToRVKPlus hc)
    (DirectSum.of (MeasuredRESKPlus hc S) 0 (measuredResClass hc (MeasuredRESObject.unit hc S))) =
      DirectSum.of (MeasuredRVKPlus hc S) 0
        (measuredRVClass hc (MeasuredRVObject.unit hc S))
  rw [DirectSum.map_of, measuredResToRVKPlus_class hc]
  rfl

theorem measuredResDirectSumToRV_mul (a b : MeasuredRESDirectSum (M := M) hc S) :
    measuredResDirectSumToRV (a * b) = measuredResDirectSumToRV a * measuredResDirectSumToRV b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [measuredResDirectSumToRV, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (MeasuredRVKPlus hc S) (i + j))
        (measuredResToRVKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance measuredResDirectSumCommMonoid : CommMonoid (MeasuredRESDirectSum (M := M) hc S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply measuredResDirectSumToRV_injective
    simp only [measuredResDirectSumToRV_mul, mul_assoc]
  one_mul a := by
    apply measuredResDirectSumToRV_injective
    simp only [measuredResDirectSumToRV_mul, measuredResDirectSumToRV_one, one_mul]
  mul_one a := by
    apply measuredResDirectSumToRV_injective
    simp only [measuredResDirectSumToRV_mul, measuredResDirectSumToRV_one, mul_one]
  mul_comm a b := by
    apply measuredResDirectSumToRV_injective
    simp only [measuredResDirectSumToRV_mul, mul_comm]

instance measuredResDirectSumCommSemiring : CommSemiring (MeasuredRESDirectSum (M := M) hc S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : MeasuredRESDirectSum hc S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def measuredResDirectSumClass (hc : CanonicalStructure.IsCanonical (M := M)) {k : ℕ} (U : MeasuredRESObject (M := M) S k) : MeasuredRESDirectSum hc S :=
  DirectSum.of (MeasuredRESKPlus hc S) k (measuredResClass hc U)

theorem measuredResDirectSumClass_product {k l : ℕ} (U : MeasuredRESObject (M := M) S k) (V : MeasuredRESObject (M := M) S l) :
    measuredResDirectSumClass hc (U.product hc V) = measuredResDirectSumClass hc U * measuredResDirectSumClass hc V := by
  rw [measuredResDirectSumClass, measuredResDirectSumClass, measuredResDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (MeasuredRESKPlus hc S) (k + l)) (measuredResClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredResGradedInclusion : MeasuredRESDirectSum (M := M) hc S →+* MeasuredRVDirectSum hc S where
  __ := measuredResDirectSumToRV
  map_one' := measuredResDirectSumToRV_one
  map_mul' := measuredResDirectSumToRV_mul

theorem measuredResGradedInclusion_injective :
    Function.Injective (measuredResGradedInclusion (M := M) (S := S) (hc := hc)) := measuredResDirectSumToRV_injective

end DiamondIntegral.Section3
