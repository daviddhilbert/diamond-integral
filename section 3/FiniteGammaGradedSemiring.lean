import «section 3».FiniteGammaPositiveComparison
import «section 3».GammaProducts
import «section 3».GammaGradedSemiring

/-! Actual graded finite Gamma products and the injective graded inclusion into Gamma. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def finiteGammaRepresentative {k : ℕ} (a : FiniteGammaKPlus (M := M) hc S k) : FiniteGammaObject hc S k :=
  Classical.choose (finiteGammaClass_surjective a)

@[simp] theorem finiteGammaRepresentative_class {k : ℕ} (a : FiniteGammaKPlus (M := M) hc S k) :
    finiteGammaClass (finiteGammaRepresentative a) = a := Classical.choose_spec (finiteGammaClass_surjective a)

def finiteGammaClassMul {k l : ℕ} (a : FiniteGammaKPlus (M := M) hc S k) (b : FiniteGammaKPlus (M := M) hc S l) : FiniteGammaKPlus hc S (k + l) :=
  finiteGammaClass ((finiteGammaRepresentative a).product (finiteGammaRepresentative b))

theorem finiteGammaToGammaKPlus_mul {k l : ℕ} (a : FiniteGammaKPlus (M := M) hc S k) (b : FiniteGammaKPlus (M := M) hc S l) :
    finiteGammaToGammaKPlus (finiteGammaClassMul a b) =
      DiamondIntegral.Section3.gammaClassMul (finiteGammaToGammaKPlus a) (finiteGammaToGammaKPlus b) := by
  have ha : gammaClass (finiteGammaRepresentative a).obj = finiteGammaToGammaKPlus a := by
    rw [← finiteGammaToGammaKPlus_class, finiteGammaRepresentative_class]
  have hb : gammaClass (finiteGammaRepresentative b).obj = finiteGammaToGammaKPlus b := by
    rw [← finiteGammaToGammaKPlus_class, finiteGammaRepresentative_class]
  change finiteGammaToGammaKPlus (finiteGammaClass ((finiteGammaRepresentative a).product (finiteGammaRepresentative b))) = _
  rw [finiteGammaToGammaKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.gammaClassMul_class
    (finiteGammaRepresentative a).obj (finiteGammaRepresentative b).obj).symm

@[simp] theorem finiteGammaClassMul_class {k l : ℕ} (U : FiniteGammaObject (M := M) hc S k) (V : FiniteGammaObject (M := M) hc S l) :
    finiteGammaClassMul (finiteGammaClass U) (finiteGammaClass V) = finiteGammaClass (U.product V) := by
  apply finiteGammaToGammaKPlus_injective
  rw [finiteGammaToGammaKPlus_mul, finiteGammaToGammaKPlus_class, finiteGammaToGammaKPlus_class, finiteGammaToGammaKPlus_class]
  exact DiamondIntegral.Section3.gammaClassMul_class U.obj V.obj

instance finiteGammaKPlusGMul : GradedMonoid.GMul (FiniteGammaKPlus (M := M) hc S) := ⟨finiteGammaClassMul⟩
instance finiteGammaKPlusGOne : GradedMonoid.GOne (FiniteGammaKPlus (M := M) hc S) := ⟨finiteGammaClass (FiniteGammaObject.unit hc S)⟩

instance finiteGammaKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (FiniteGammaKPlus (M := M) hc S) where
  mul_zero a := by
    change finiteGammaClassMul a 0 = 0
    apply finiteGammaToGammaKPlus_injective
    simp only [finiteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := GammaKPlus hc S) _
  zero_mul b := by
    change finiteGammaClassMul 0 b = 0
    apply finiteGammaToGammaKPlus_injective
    simp only [finiteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := GammaKPlus hc S) _
  mul_add a b c := by
    change finiteGammaClassMul a (b + c) = finiteGammaClassMul a b + finiteGammaClassMul a c
    apply finiteGammaToGammaKPlus_injective
    simp only [finiteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := GammaKPlus hc S) _ _ _
  add_mul a b c := by
    change finiteGammaClassMul (a + b) c = finiteGammaClassMul a c + finiteGammaClassMul b c
    apply finiteGammaToGammaKPlus_injective
    simp only [finiteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := GammaKPlus hc S) _ _ _

abbrev FiniteGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) := DirectSum ℕ (FiniteGammaKPlus (M := M) hc S)

def finiteGammaDirectSumToGamma : FiniteGammaDirectSum (M := M) hc S →+
    DiamondIntegral.Section3.GammaDirectSum (M := M) hc S :=
  DirectSum.map (fun _ => finiteGammaToGammaKPlus)

theorem finiteGammaDirectSumToGamma_injective : Function.Injective (finiteGammaDirectSumToGamma (M := M) (hc := hc) (S := S)) :=
  (DirectSum.map_injective (fun _ => finiteGammaToGammaKPlus)).mpr (fun _ => finiteGammaToGammaKPlus_injective)

theorem finiteGammaDirectSumToGamma_one : finiteGammaDirectSumToGamma (1 : FiniteGammaDirectSum (M := M) hc S) = 1 := by
  change DirectSum.map (fun _ => finiteGammaToGammaKPlus)
    (DirectSum.of (FiniteGammaKPlus hc S) 0 (finiteGammaClass (FiniteGammaObject.unit hc S))) =
      DirectSum.of (DiamondIntegral.Section3.GammaKPlus hc S) 0
        (DiamondIntegral.Section3.gammaClass (GammaObject.unit hc S))
  rw [DirectSum.map_of, finiteGammaToGammaKPlus_class]
  rfl

theorem finiteGammaDirectSumToGamma_mul (a b : FiniteGammaDirectSum (M := M) hc S) :
    finiteGammaDirectSumToGamma (a * b) = finiteGammaDirectSumToGamma a * finiteGammaDirectSumToGamma b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [finiteGammaDirectSumToGamma, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.GammaKPlus hc S) (i + j))
        (finiteGammaToGammaKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance finiteGammaDirectSumCommMonoid : CommMonoid (FiniteGammaDirectSum (M := M) hc S) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply finiteGammaDirectSumToGamma_injective
    simp only [finiteGammaDirectSumToGamma_mul, mul_assoc]
  one_mul a := by
    apply finiteGammaDirectSumToGamma_injective
    simp only [finiteGammaDirectSumToGamma_mul, finiteGammaDirectSumToGamma_one, one_mul]
  mul_one a := by
    apply finiteGammaDirectSumToGamma_injective
    simp only [finiteGammaDirectSumToGamma_mul, finiteGammaDirectSumToGamma_one, mul_one]
  mul_comm a b := by
    apply finiteGammaDirectSumToGamma_injective
    rw [finiteGammaDirectSumToGamma_mul, finiteGammaDirectSumToGamma_mul]
    exact mul_comm _ _

instance finiteGammaDirectSumCommSemiring : CommSemiring (FiniteGammaDirectSum (M := M) hc S) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : FiniteGammaDirectSum hc S)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def finiteGammaDirectSumClass {k : ℕ} (U : FiniteGammaObject (M := M) hc S k) : FiniteGammaDirectSum hc S :=
  DirectSum.of (FiniteGammaKPlus hc S) k (finiteGammaClass U)

theorem finiteGammaDirectSumClass_product {k l : ℕ} (U : FiniteGammaObject (M := M) hc S k) (V : FiniteGammaObject (M := M) hc S l) :
    finiteGammaDirectSumClass (U.product V) = finiteGammaDirectSumClass U * finiteGammaDirectSumClass V := by
  rw [finiteGammaDirectSumClass, finiteGammaDirectSumClass, finiteGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (FiniteGammaKPlus hc S) (k + l)) (finiteGammaClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def finiteGammaGradedInclusion : FiniteGammaDirectSum (M := M) hc S →+* GammaDirectSum hc S where
  __ := finiteGammaDirectSumToGamma
  map_one' := finiteGammaDirectSumToGamma_one
  map_mul' := finiteGammaDirectSumToGamma_mul

theorem finiteGammaGradedInclusion_injective :
    Function.Injective (finiteGammaGradedInclusion (M := M) (hc := hc) (S := S)) := finiteGammaDirectSumToGamma_injective

end DiamondIntegral.Section3
