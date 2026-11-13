import «section 3».GammaGroundMeasuredFiniteGammaPositiveComparison
import «section 3».GammaGroundMeasuredGammaProducts
import «section 3».GammaGroundMeasuredGammaGradedSemiring
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

def gammaGroundMeasuredFiniteGammaRepresentative {k : ℕ} (a : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground k) : GammaGroundMeasuredFiniteGammaObject hc ground k :=
  Classical.choose (gammaGroundMeasuredFiniteGammaClass_surjective a)

@[simp] theorem gammaGroundMeasuredFiniteGammaRepresentative_class {k : ℕ} (a : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground k) :
    gammaGroundMeasuredFiniteGammaClass (gammaGroundMeasuredFiniteGammaRepresentative a) = a := Classical.choose_spec (gammaGroundMeasuredFiniteGammaClass_surjective a)

def gammaGroundMeasuredFiniteGammaClassMul {k l : ℕ} (a : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground k) (b : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground l) : GammaGroundMeasuredFiniteGammaKPlus hc ground (k + l) :=
  gammaGroundMeasuredFiniteGammaClass ((gammaGroundMeasuredFiniteGammaRepresentative a).product (gammaGroundMeasuredFiniteGammaRepresentative b))

theorem gammaGroundMeasuredFiniteGammaToGammaKPlus_mul {k l : ℕ} (a : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground k) (b : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground l) :
    gammaGroundMeasuredFiniteGammaToGammaKPlus (gammaGroundMeasuredFiniteGammaClassMul a b) =
      DiamondIntegral.Section3.gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredFiniteGammaToGammaKPlus a) (gammaGroundMeasuredFiniteGammaToGammaKPlus b) := by
  have ha : gammaGroundMeasuredGammaClass (gammaGroundMeasuredFiniteGammaRepresentative a).obj = gammaGroundMeasuredFiniteGammaToGammaKPlus a := by
    rw [← gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredFiniteGammaRepresentative_class]
  have hb : gammaGroundMeasuredGammaClass (gammaGroundMeasuredFiniteGammaRepresentative b).obj = gammaGroundMeasuredFiniteGammaToGammaKPlus b := by
    rw [← gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredFiniteGammaRepresentative_class]
  change gammaGroundMeasuredFiniteGammaToGammaKPlus (gammaGroundMeasuredFiniteGammaClass ((gammaGroundMeasuredFiniteGammaRepresentative a).product (gammaGroundMeasuredFiniteGammaRepresentative b))) = _
  rw [gammaGroundMeasuredFiniteGammaToGammaKPlus_class, ← ha, ← hb]
  exact (DiamondIntegral.Section3.gammaGroundMeasuredGammaClassMul_class
    (gammaGroundMeasuredFiniteGammaRepresentative a).obj (gammaGroundMeasuredFiniteGammaRepresentative b).obj).symm

@[simp] theorem gammaGroundMeasuredFiniteGammaClassMul_class {k l : ℕ} (U : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground k) (V : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground l) :
    gammaGroundMeasuredFiniteGammaClassMul (gammaGroundMeasuredFiniteGammaClass U) (gammaGroundMeasuredFiniteGammaClass V) = gammaGroundMeasuredFiniteGammaClass (U.product V) := by
  apply gammaGroundMeasuredFiniteGammaToGammaKPlus_injective
  rw [gammaGroundMeasuredFiniteGammaToGammaKPlus_mul, gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredFiniteGammaToGammaKPlus_class, gammaGroundMeasuredFiniteGammaToGammaKPlus_class]
  exact DiamondIntegral.Section3.gammaGroundMeasuredGammaClassMul_class U.obj V.obj

instance gammaGroundMeasuredFiniteGammaKPlusGMul : GradedMonoid.GMul (GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground) := ⟨gammaGroundMeasuredFiniteGammaClassMul⟩
instance gammaGroundMeasuredFiniteGammaKPlusGOne : GradedMonoid.GOne (GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground) := ⟨gammaGroundMeasuredFiniteGammaClass (GammaGroundMeasuredFiniteGammaObject.unit hc ground)⟩

instance gammaGroundMeasuredFiniteGammaKPlusDistributivity : DirectSum.GNonUnitalNonAssocSemiring (GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground) where
  mul_zero a := by
    change gammaGroundMeasuredFiniteGammaClassMul a 0 = 0
    apply gammaGroundMeasuredFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundMeasuredFiniteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero (A := GammaGroundMeasuredGammaKPlus hc ground) _
  zero_mul b := by
    change gammaGroundMeasuredFiniteGammaClassMul 0 b = 0
    apply gammaGroundMeasuredFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundMeasuredFiniteGammaToGammaKPlus_mul, map_zero]
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul (A := GammaGroundMeasuredGammaKPlus hc ground) _
  mul_add a b c := by
    change gammaGroundMeasuredFiniteGammaClassMul a (b + c) = gammaGroundMeasuredFiniteGammaClassMul a b + gammaGroundMeasuredFiniteGammaClassMul a c
    apply gammaGroundMeasuredFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundMeasuredFiniteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add (A := GammaGroundMeasuredGammaKPlus hc ground) _ _ _
  add_mul a b c := by
    change gammaGroundMeasuredFiniteGammaClassMul (a + b) c = gammaGroundMeasuredFiniteGammaClassMul a c + gammaGroundMeasuredFiniteGammaClassMul b c
    apply gammaGroundMeasuredFiniteGammaToGammaKPlus_injective
    simp only [gammaGroundMeasuredFiniteGammaToGammaKPlus_mul, map_add]
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul (A := GammaGroundMeasuredGammaKPlus hc ground) _ _ _

abbrev GammaGroundMeasuredFiniteGammaDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := DirectSum ℕ (GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground)

def gammaGroundMeasuredFiniteGammaDirectSumToGamma : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground →+
    DiamondIntegral.Section3.GammaGroundMeasuredGammaDirectSum (M := M) hc ground :=
  DirectSum.map (fun _ => gammaGroundMeasuredFiniteGammaToGammaKPlus)

theorem gammaGroundMeasuredFiniteGammaDirectSumToGamma_injective : Function.Injective (gammaGroundMeasuredFiniteGammaDirectSumToGamma (M := M) (hc := hc) (ground := ground)) :=
  (DirectSum.map_injective (fun _ => gammaGroundMeasuredFiniteGammaToGammaKPlus)).mpr (fun _ => gammaGroundMeasuredFiniteGammaToGammaKPlus_injective)

theorem gammaGroundMeasuredFiniteGammaDirectSumToGamma_one : gammaGroundMeasuredFiniteGammaDirectSumToGamma (1 : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) = 1 := by
  change DirectSum.map (fun _ => gammaGroundMeasuredFiniteGammaToGammaKPlus)
    (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) 0 (gammaGroundMeasuredFiniteGammaClass (GammaGroundMeasuredFiniteGammaObject.unit hc ground))) =
      DirectSum.of (DiamondIntegral.Section3.GammaGroundMeasuredGammaKPlus hc ground) 0
        (DiamondIntegral.Section3.gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.unit hc ground))
  rw [DirectSum.map_of, gammaGroundMeasuredFiniteGammaToGammaKPlus_class]
  rfl

theorem gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul (a b : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) :
    gammaGroundMeasuredFiniteGammaDirectSumToGamma (a * b) = gammaGroundMeasuredFiniteGammaDirectSumToGamma a * gammaGroundMeasuredFiniteGammaDirectSumToGamma b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      simp only [gammaGroundMeasuredFiniteGammaDirectSumToGamma, DirectSum.of_mul_of, DirectSum.map_of]
      exact congrArg (DirectSum.of (DiamondIntegral.Section3.GammaGroundMeasuredGammaKPlus hc ground) (i + j))
        (gammaGroundMeasuredFiniteGammaToGammaKPlus_mul a b)
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

instance gammaGroundMeasuredFiniteGammaDirectSumCommMonoid : CommMonoid (GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := by
    apply gammaGroundMeasuredFiniteGammaDirectSumToGamma_injective
    simp only [gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul, mul_assoc]
  one_mul a := by
    apply gammaGroundMeasuredFiniteGammaDirectSumToGamma_injective
    simp only [gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul, gammaGroundMeasuredFiniteGammaDirectSumToGamma_one, one_mul]
  mul_one a := by
    apply gammaGroundMeasuredFiniteGammaDirectSumToGamma_injective
    simp only [gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul, gammaGroundMeasuredFiniteGammaDirectSumToGamma_one, mul_one]
  mul_comm a b := by
    apply gammaGroundMeasuredFiniteGammaDirectSumToGamma_injective
    rw [gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul, gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul]
    exact mul_comm _ _

instance gammaGroundMeasuredFiniteGammaDirectSumCommSemiring : CommSemiring (GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) where
  toAddCommMonoid := inferInstance
  toCommMonoid := inferInstance
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
  natCast n := n • (1 : GammaGroundMeasuredFiniteGammaDirectSum hc ground)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul, one_nsmul]

def gammaGroundMeasuredFiniteGammaDirectSumClass {k : ℕ} (U : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground k) : GammaGroundMeasuredFiniteGammaDirectSum hc ground :=
  DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass U)

theorem gammaGroundMeasuredFiniteGammaDirectSumClass_product {k l : ℕ} (U : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground k) (V : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground l) :
    gammaGroundMeasuredFiniteGammaDirectSumClass (U.product V) = gammaGroundMeasuredFiniteGammaDirectSumClass U * gammaGroundMeasuredFiniteGammaDirectSumClass V := by
  rw [gammaGroundMeasuredFiniteGammaDirectSumClass, gammaGroundMeasuredFiniteGammaDirectSumClass, gammaGroundMeasuredFiniteGammaDirectSumClass, DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) (k + l)) (gammaGroundMeasuredFiniteGammaClassMul_class U V).symm

end DiamondIntegral.Section3

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def gammaGroundMeasuredFiniteGammaGradedInclusion : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground →+* GammaGroundMeasuredGammaDirectSum hc ground where
  __ := gammaGroundMeasuredFiniteGammaDirectSumToGamma
  map_one' := gammaGroundMeasuredFiniteGammaDirectSumToGamma_one
  map_mul' := gammaGroundMeasuredFiniteGammaDirectSumToGamma_mul

theorem gammaGroundMeasuredFiniteGammaGradedInclusion_injective :
    Function.Injective (gammaGroundMeasuredFiniteGammaGradedInclusion (M := M) (hc := hc) (ground := ground)) := gammaGroundMeasuredFiniteGammaDirectSumToGamma_injective

end DiamondIntegral.Section3
