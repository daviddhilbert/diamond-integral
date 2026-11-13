import «section 3».MeasuredFiniteGammaPositiveComparison
import «section 3».MeasuredGammaProducts
import «section 3».MeasuredGammaGradedSemiring

/-! Actual graded finite Gamma products and the injective graded inclusion into Gamma. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredFiniteGammaRepresentative {k : ℕ} (a : MeasuredFiniteGammaKPlus (M := M) hc S k) : MeasuredFiniteGammaObject hc S k :=
  Classical.choose (measuredFiniteGammaClass_surjective a)

@[simp] theorem measuredFiniteGammaRepresentative_class {k : ℕ} (a : MeasuredFiniteGammaKPlus (M := M) hc S k) :
    measuredFiniteGammaClass (measuredFiniteGammaRepresentative a) = a := Classical.choose_spec (measuredFiniteGammaClass_surjective a)

def measuredFiniteGammaClassMul {k l : ℕ} (a : MeasuredFiniteGammaKPlus (M := M) hc S k) (b : MeasuredFiniteGammaKPlus (M := M) hc S l) : MeasuredFiniteGammaKPlus hc S (k + l) :=
  measuredFiniteGammaClass ((measuredFiniteGammaRepresentative a).product (measuredFiniteGammaRepresentative b))

theorem measuredFiniteGammaToGammaKPlus_mul {k l : ℕ} (a : MeasuredFiniteGammaKPlus (M := M) hc S k) (b : MeasuredFiniteGammaKPlus (M := M) hc S l) :
    measuredFiniteGammaToGammaKPlus (measuredFiniteGammaClassMul a b) =
      DiamondIntegral.Section3.measuredGammaClassMul (measuredFiniteGammaToGammaKPlus a) (measuredFiniteGammaToGammaKPlus b) := by
  have ha : measuredGammaClass (measuredFiniteGammaRepresentative a).obj = measuredFiniteGammaToGammaKPlus a := by
    rw [← measuredFiniteGammaToGammaKPlus_class, measuredFiniteGammaRepresentative_class]
  have hb : measuredGammaClass (measuredFiniteGammaRepresentative b).obj = measuredFiniteGammaToGammaKPlus b := by
    rw [← measuredFiniteGammaToGammaKPlus_class, measuredFiniteGammaRepresentative_class]
  change measuredFiniteGammaToGammaKPlus (measuredFiniteGammaClass ((measuredFiniteGammaRepresentative a).product (measuredFiniteGammaRepresentative b))) = _
  rw [measuredFiniteGammaToGammaKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.measuredGammaClassMul_class
    (measuredFiniteGammaRepresentative a).obj (measuredFiniteGammaRepresentative b).obj).symm

@[simp] theorem measuredFiniteGammaClassMul_class {k l : ℕ} (U : MeasuredFiniteGammaObject (M := M) hc S k) (V : MeasuredFiniteGammaObject (M := M) hc S l) :
    measuredFiniteGammaClassMul (measuredFiniteGammaClass U) (measuredFiniteGammaClass V) = measuredFiniteGammaClass (U.product V) := by
  apply measuredFiniteGammaToGammaKPlus_injective
  rw [measuredFiniteGammaToGammaKPlus_mul, measuredFiniteGammaToGammaKPlus_class, measuredFiniteGammaToGammaKPlus_class, measuredFiniteGammaToGammaKPlus_class]
  exact DiamondIntegral.Section3.measuredGammaClassMul_class U.obj V.obj

instance measuredFiniteGammaKPlusGMul : GradedMonoid.GMul (MeasuredFiniteGammaKPlus (M := M) hc S) := ⟨measuredFiniteGammaClassMul⟩
instance measuredFiniteGammaKPlusGOne : GradedMonoid.GOne (MeasuredFiniteGammaKPlus (M := M) hc S) := ⟨measuredFiniteGammaClass (MeasuredFiniteGammaObject.unit hc S)⟩

instance measuredFiniteGammaKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (MeasuredFiniteGammaKPlus (M := M) hc S) where
  mul_zero a := by
    change measuredFiniteGammaClassMul a 0 = 0
    apply measuredFiniteGammaToGammaKPlus_injective
    simp only [measuredFiniteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := MeasuredGammaKPlus hc S) _
  zero_mul b := by
    change measuredFiniteGammaClassMul 0 b = 0
    apply measuredFiniteGammaToGammaKPlus_injective
    simp only [measuredFiniteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := MeasuredGammaKPlus hc S) _
  mul_add a b c := by
    change measuredFiniteGammaClassMul a (b + c) = measuredFiniteGammaClassMul a b + measuredFiniteGammaClassMul a c
    apply measuredFiniteGammaToGammaKPlus_injective
    simp only [measuredFiniteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := MeasuredGammaKPlus hc S) _ _ _
  add_mul a b c := by
    change measuredFiniteGammaClassMul (a + b) c = measuredFiniteGammaClassMul a c + measuredFiniteGammaClassMul b c
    apply measuredFiniteGammaToGammaKPlus_injective
    simp only [measuredFiniteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := MeasuredGammaKPlus hc S) _ _ _

abbrev MeasuredFiniteGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) := DirectSum ℕ (MeasuredFiniteGammaKPlus (M := M) hc S)

def measuredFiniteGammaDirectSumToGamma : MeasuredFiniteGammaDirectSum (M := M) hc S →+
    DiamondIntegral.Section3.MeasuredGammaDirectSum (M := M) hc S :=
  DirectSum.map (fun _ => measuredFiniteGammaToGammaKPlus)

theorem measuredFiniteGammaDirectSumToGamma_injective : Function.Injective (measuredFiniteGammaDirectSumToGamma (M := M) (hc := hc) (S := S)) :=
  (DirectSum.map_injective (fun _ => measuredFiniteGammaToGammaKPlus)).mpr (fun _ => measuredFiniteGammaToGammaKPlus_injective)

theorem measuredFiniteGammaDirectSumToGamma_one : measuredFiniteGammaDirectSumToGamma (1 : MeasuredFiniteGammaDirectSum (M := M) hc S) = 1 := by
  change DirectSum.map (fun _ => measuredFiniteGammaToGammaKPlus)
    (DirectSum.of (MeasuredFiniteGammaKPlus hc S) 0 (measuredFiniteGammaClass (MeasuredFiniteGammaObject.unit hc S))) =
      DirectSum.of (DiamondIntegral.Section3.MeasuredGammaKPlus hc S) 0
        (DiamondIntegral.Section3.measuredGammaClass (MeasuredGammaObject.unit hc S))
  rw [DirectSum.map_of, measuredFiniteGammaToGammaKPlus_class]
  rfl

theorem measuredFiniteGammaDirectSumToGamma_mul (a b : MeasuredFiniteGammaDirectSum (M := M) hc S) :
    measuredFiniteGammaDirectSumToGamma (a * b) = measuredFiniteGammaDirectSumToGamma a * measuredFiniteGammaDirectSumToGamma b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [measuredFiniteGammaDirectSumToGamma, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.MeasuredGammaKPlus hc S) (i + j))
        (measuredFiniteGammaToGammaKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance measuredFiniteGammaDirectSumCommMonoid : CommMonoid (MeasuredFiniteGammaDirectSum (M := M) hc S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply measuredFiniteGammaDirectSumToGamma_injective
    simp only [measuredFiniteGammaDirectSumToGamma_mul, mul_assoc]
  one_mul a := by
    apply measuredFiniteGammaDirectSumToGamma_injective
    simp only [measuredFiniteGammaDirectSumToGamma_mul, measuredFiniteGammaDirectSumToGamma_one, one_mul]
  mul_one a := by
    apply measuredFiniteGammaDirectSumToGamma_injective
    simp only [measuredFiniteGammaDirectSumToGamma_mul, measuredFiniteGammaDirectSumToGamma_one, mul_one]
  mul_comm a b := by
    apply measuredFiniteGammaDirectSumToGamma_injective
    rw [measuredFiniteGammaDirectSumToGamma_mul, measuredFiniteGammaDirectSumToGamma_mul]
    exact mul_comm _ _

instance measuredFiniteGammaDirectSumCommSemiring : CommSemiring (MeasuredFiniteGammaDirectSum (M := M) hc S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : MeasuredFiniteGammaDirectSum hc S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def measuredFiniteGammaDirectSumClass {k : ℕ} (U : MeasuredFiniteGammaObject (M := M) hc S k) : MeasuredFiniteGammaDirectSum hc S :=
  DirectSum.of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass U)

theorem measuredFiniteGammaDirectSumClass_product {k l : ℕ} (U : MeasuredFiniteGammaObject (M := M) hc S k) (V : MeasuredFiniteGammaObject (M := M) hc S l) :
    measuredFiniteGammaDirectSumClass (U.product V) = measuredFiniteGammaDirectSumClass U * measuredFiniteGammaDirectSumClass V := by
  rw [measuredFiniteGammaDirectSumClass, measuredFiniteGammaDirectSumClass, measuredFiniteGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (MeasuredFiniteGammaKPlus hc S) (k + l)) (measuredFiniteGammaClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredFiniteGammaGradedInclusion : MeasuredFiniteGammaDirectSum (M := M) hc S →+* MeasuredGammaDirectSum hc S where
  __ := measuredFiniteGammaDirectSumToGamma
  map_one' := measuredFiniteGammaDirectSumToGamma_one
  map_mul' := measuredFiniteGammaDirectSumToGamma_mul

theorem measuredFiniteGammaGradedInclusion_injective :
    Function.Injective (measuredFiniteGammaGradedInclusion (M := M) (hc := hc) (S := S)) := measuredFiniteGammaDirectSumToGamma_injective

end DiamondIntegral.Section3
