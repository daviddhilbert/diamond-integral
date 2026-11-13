import «section 3».RESCoproducts
import «section 3».RVGradedSemiring

/-! Actual graded RES products and the injective graded inclusion into RV. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def RESObject.unit (S : Set M) : RESObject (M := M) S 0 :=
  ⟨RVObject.unit S, (RVObject.unit S).degree_zero_res⟩

def resRepresentative {k : ℕ} (a : RESKPlus (M := M) S k) : RESObject S k :=
  Classical.choose (resClass_surjective a)

@[simp] theorem resRepresentative_class {k : ℕ} (a : RESKPlus (M := M) S k) :
    resClass (resRepresentative a) = a := Classical.choose_spec (resClass_surjective a)

def resClassMul {k l : ℕ} (a : RESKPlus (M := M) S k) (b : RESKPlus (M := M) S l) : RESKPlus S (k + l) :=
  resClass ((resRepresentative a).product (resRepresentative b))

theorem resToRVKPlus_mul {k l : ℕ} (a : RESKPlus (M := M) S k) (b : RESKPlus (M := M) S l) :
    resToRVKPlus (resClassMul a b) =
      DiamondIntegral.Section3.rvClassMul (resToRVKPlus a) (resToRVKPlus b) := by
  have ha : rvClass (resRepresentative a).obj = resToRVKPlus a := by
    rw [← resToRVKPlus_class, resRepresentative_class]
  have hb : rvClass (resRepresentative b).obj = resToRVKPlus b := by
    rw [← resToRVKPlus_class, resRepresentative_class]
  change resToRVKPlus (resClass ((resRepresentative a).product (resRepresentative b))) = _
  rw [resToRVKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.rvClassMul_class
    (resRepresentative a).obj (resRepresentative b).obj).symm

@[simp] theorem resClassMul_class {k l : ℕ} (U : RESObject (M := M) S k) (V : RESObject (M := M) S l) :
    resClassMul (resClass U) (resClass V) = resClass (U.product V) := by
  apply resToRVKPlus_injective
  rw [resToRVKPlus_mul, resToRVKPlus_class, resToRVKPlus_class, resToRVKPlus_class]
  exact DiamondIntegral.Section3.rvClassMul_class U.obj V.obj

instance resKPlusGMul : GradedMonoid.GMul (RESKPlus (M := M) S) := ⟨resClassMul⟩
instance resKPlusGOne : GradedMonoid.GOne (RESKPlus (M := M) S) := ⟨resClass (RESObject.unit S)⟩

instance resKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (RESKPlus (M := M) S) where
  mul_zero a := by
    change resClassMul a 0 = 0
    apply resToRVKPlus_injective
    simp only [resToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := RVKPlus S) _
  zero_mul b := by
    change resClassMul 0 b = 0
    apply resToRVKPlus_injective
    simp only [resToRVKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := RVKPlus S) _
  mul_add a b c := by
    change resClassMul a (b + c) = resClassMul a b + resClassMul a c
    apply resToRVKPlus_injective
    simp only [resToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := RVKPlus S) _ _ _
  add_mul a b c := by
    change resClassMul (a + b) c = resClassMul a c + resClassMul b c
    apply resToRVKPlus_injective
    simp only [resToRVKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := RVKPlus S) _ _ _

abbrev RESDirectSum (S : Set M) := DirectSum ℕ (RESKPlus (M := M) S)

def resDirectSumToRV : RESDirectSum (M := M) S →+
    DiamondIntegral.Section3.RVDirectSum (M := M) S :=
  DirectSum.map (fun _ => resToRVKPlus)

theorem resDirectSumToRV_injective : Function.Injective (resDirectSumToRV (M := M) (S := S)) :=
  (DirectSum.map_injective (fun _ => resToRVKPlus)).mpr (fun _ => resToRVKPlus_injective)

theorem resDirectSumToRV_one : resDirectSumToRV (1 : RESDirectSum (M := M) S) = 1 := by
  change DirectSum.map (fun _ => resToRVKPlus)
    (DirectSum.of (RESKPlus S) 0 (resClass (RESObject.unit S))) =
      DirectSum.of (DiamondIntegral.Section3.RVKPlus S) 0
        (DiamondIntegral.Section3.rvClass (RVObject.unit S))
  rw [DirectSum.map_of, resToRVKPlus_class]
  rfl

theorem resDirectSumToRV_mul (a b : RESDirectSum (M := M) S) :
    resDirectSumToRV (a * b) = resDirectSumToRV a * resDirectSumToRV b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [resDirectSumToRV, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.RVKPlus S) (i + j))
        (resToRVKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance resDirectSumCommMonoid : CommMonoid (RESDirectSum (M := M) S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply resDirectSumToRV_injective
    simp only [resDirectSumToRV_mul, mul_assoc]
  one_mul a := by
    apply resDirectSumToRV_injective
    simp only [resDirectSumToRV_mul, resDirectSumToRV_one, one_mul]
  mul_one a := by
    apply resDirectSumToRV_injective
    simp only [resDirectSumToRV_mul, resDirectSumToRV_one, mul_one]
  mul_comm a b := by
    apply resDirectSumToRV_injective
    simp only [resDirectSumToRV_mul, mul_comm]

instance resDirectSumCommSemiring : CommSemiring (RESDirectSum (M := M) S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : RESDirectSum S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def resDirectSumClass {k : ℕ} (U : RESObject (M := M) S k) : RESDirectSum S :=
  DirectSum.of (RESKPlus S) k (resClass U)

theorem resDirectSumClass_product {k l : ℕ} (U : RESObject (M := M) S k) (V : RESObject (M := M) S l) :
    resDirectSumClass (U.product V) = resDirectSumClass U * resDirectSumClass V := by
  rw [resDirectSumClass, resDirectSumClass, resDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (RESKPlus S) (k + l)) (resClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def resGradedInclusion : RESDirectSum (M := M) S →+* RVDirectSum S where
  __ := resDirectSumToRV
  map_one' := resDirectSumToRV_one
  map_mul' := resDirectSumToRV_mul

theorem resGradedInclusion_injective :
    Function.Injective (resGradedInclusion (M := M) (S := S)) := resDirectSumToRV_injective

end DiamondIntegral.Section3
