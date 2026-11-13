import «section 3».RVPositiveComparison
import «section 3».RVProducts
import «section 3».RVSemiring
import Section4.RVGradedSemiring

/-! The direct sum of the actual fixed-degree positive RV quotients is
a commutative semiring. Its multiplication comes from genuine cartesian
products and is verified through an injective map to the checked ambient
presentation. No cancellation or geometric kernel premise is assumed. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rvRepresentative {k : ℕ} (a : RVKPlus (M := M) S k) : RVObject S k :=
  Classical.choose (rvClass_surjective a)

@[simp] theorem rvRepresentative_class {k : ℕ} (a : RVKPlus (M := M) S k) :
    rvClass (rvRepresentative a) = a := Classical.choose_spec (rvClass_surjective a)

def rvClassMul {k l : ℕ} (a : RVKPlus (M := M) S k) (b : RVKPlus (M := M) S l) : RVKPlus S (k + l) :=
  rvClass ((rvRepresentative a).product (rvRepresentative b))

theorem rvToAmbientKPlus_mul {k l : ℕ} (a : RVKPlus (M := M) S k) (b : RVKPlus (M := M) S l) :
    rvToAmbientKPlus (rvClassMul a b) =
      SpecialTransformations.Section4.rvClassMul (rvToAmbientKPlus a) (rvToAmbientKPlus b) := by
  have ha : rvAmbientClass (rvRepresentative a) = rvToAmbientKPlus a := by
    rw [← rvToAmbientKPlus_class, rvRepresentative_class]
  have hb : rvAmbientClass (rvRepresentative b) = rvToAmbientKPlus b := by
    rw [← rvToAmbientKPlus_class, rvRepresentative_class]
  change rvToAmbientKPlus (rvClass ((rvRepresentative a).product (rvRepresentative b))) = _
  rw [rvToAmbientKPlus_class, ← ha, ← hb]
  exact (SpecialTransformations.Section4.rvClassMul_class
    (rvRepresentative a).toCompanion.obj (rvRepresentative b).toCompanion.obj).symm

@[simp] theorem rvClassMul_class {k l : ℕ} (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    rvClassMul (rvClass U) (rvClass V) = rvClass (U.product V) := by
  apply rvToAmbientKPlus_injective
  rw [rvToAmbientKPlus_mul, rvToAmbientKPlus_class, rvToAmbientKPlus_class, rvToAmbientKPlus_class]
  exact SpecialTransformations.Section4.rvClassMul_class U.toCompanion.obj V.toCompanion.obj

instance rvKPlusGMul : GradedMonoid.GMul (RVKPlus (M := M) S) := ⟨rvClassMul⟩
instance rvKPlusGOne : GradedMonoid.GOne (RVKPlus (M := M) S) := ⟨rvClass (RVObject.unit S)⟩

instance rvKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (RVKPlus (M := M) S) where
  mul_zero a := by
    change rvClassMul a 0 = 0
    apply rvToAmbientKPlus_injective
    simp only [rvToAmbientKPlus_mul, map_zero, SpecialTransformations.Section4.rvClassMul_zero]
  zero_mul b := by
    change rvClassMul 0 b = 0
    apply rvToAmbientKPlus_injective
    simp only [rvToAmbientKPlus_mul, map_zero, SpecialTransformations.Section4.rvClassMul_zero_left]
  mul_add a b c := by
    change rvClassMul a (b + c) = rvClassMul a b + rvClassMul a c
    apply rvToAmbientKPlus_injective
    simp only [rvToAmbientKPlus_mul, map_add, SpecialTransformations.Section4.rvClassMul_add]
  add_mul a b c := by
    change rvClassMul (a + b) c = rvClassMul a c + rvClassMul b c
    apply rvToAmbientKPlus_injective
    simp only [rvToAmbientKPlus_mul, map_add, SpecialTransformations.Section4.rvClassMul_add_left]

abbrev RVDirectSum (S : Set M) := DirectSum ℕ (RVKPlus (M := M) S)

def rvDirectSumToAmbient : RVDirectSum (M := M) S →+
    SpecialTransformations.Section4.RVGradedKPlus (M := M) S :=
  DirectSum.map (fun _ => rvToAmbientKPlus)

theorem rvDirectSumToAmbient_injective : Function.Injective (rvDirectSumToAmbient (M := M) (S := S)) :=
  (DirectSum.map_injective (fun _ => rvToAmbientKPlus)).mpr (fun _ => rvToAmbientKPlus_injective)

theorem rvDirectSumToAmbient_one : rvDirectSumToAmbient (1 : RVDirectSum (M := M) S) = 1 := by
  change DirectSum.map (fun _ => rvToAmbientKPlus)
    (DirectSum.of (RVKPlus S) 0 (rvClass (RVObject.unit S))) =
      DirectSum.of (SpecialTransformations.Section4.RVKPlus S) 0
        (SpecialTransformations.Section4.rvClass (rvUnitObject S))
  rw [DirectSum.map_of, rvToAmbientKPlus_class]
  rfl

theorem rvDirectSumToAmbient_mul (a b : RVDirectSum (M := M) S) :
    rvDirectSumToAmbient (a * b) = rvDirectSumToAmbient a * rvDirectSumToAmbient b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [rvDirectSumToAmbient, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (SpecialTransformations.Section4.RVKPlus S) (i + j))
        (rvToAmbientKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance rvDirectSumCommMonoid : CommMonoid (RVDirectSum (M := M) S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply rvDirectSumToAmbient_injective
    simp only [rvDirectSumToAmbient_mul, mul_assoc]
  one_mul a := by
    apply rvDirectSumToAmbient_injective
    simp only [rvDirectSumToAmbient_mul, rvDirectSumToAmbient_one, one_mul]
  mul_one a := by
    apply rvDirectSumToAmbient_injective
    simp only [rvDirectSumToAmbient_mul, rvDirectSumToAmbient_one, mul_one]
  mul_comm a b := by
    apply rvDirectSumToAmbient_injective
    simp only [rvDirectSumToAmbient_mul, mul_comm]

instance rvDirectSumCommSemiring : CommSemiring (RVDirectSum (M := M) S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : RVDirectSum S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def rvDirectSumClass {k : ℕ} (U : RVObject (M := M) S k) : RVDirectSum S :=
  DirectSum.of (RVKPlus S) k (rvClass U)

theorem rvDirectSumClass_product {k l : ℕ} (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    rvDirectSumClass (U.product V) = rvDirectSumClass U * rvDirectSumClass V := by
  rw [rvDirectSumClass, rvDirectSumClass, rvDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (RVKPlus S) (k + l)) (rvClassMul_class U V).symm

end DiamondIntegral.Section3
