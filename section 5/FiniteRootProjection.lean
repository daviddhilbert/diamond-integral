import «section 5».CompatibleRootSystems
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Every finite Kummer multiplier is the projection of an actual compatible
root system. A single complex winding character provides the required lifts. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Complex Real

def complexWindingCharacter : Multiplicative ℚ →* ℂˣ where
  toFun q := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * (q.toAdd : ℂ))) (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    simp
  map_mul' q r := by
    apply Units.ext
    simp [mul_add, Complex.exp_add]

theorem complexWindingCharacter_one : complexWindingCharacter (Multiplicative.ofAdd 1) = 1 := by
  apply Units.ext
  change Complex.exp (2 * Real.pi * Complex.I * (1 : ℚ)) = 1
  simpa using Complex.exp_two_pi_mul_I

def windingRootSystem : CompatibleRoots ℂ :=
  rationalCharacterSystem complexWindingCharacter complexWindingCharacter_one

theorem windingRootSystem_primitive (n : ℕ+) :
    IsPrimitiveRoot ((windingRootSystem.val n : ℂˣ) : ℂ) (n : ℕ) := by
  change IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / (n : ℕ)) : ℚ))) (n : ℕ)
  convert Complex.isPrimitiveRoot_exp (n : ℕ) n.ne_zero using 1
  push_cast
  congr 1
  ring

def finiteRootProjection (n : ℕ+) : CompatibleRoots ℂ →* rootsOfUnity (n : ℕ) ℂ where
  toFun η := ⟨η.val n, η.property.1 n⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem finiteRootProjection_surjective (n : ℕ+) : Function.Surjective (finiteRootProjection n) := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  intro ζ
  obtain ⟨j, _, hj⟩ := (windingRootSystem_primitive n).eq_pow_of_pow_eq_one
    ((mem_rootsOfUnity' (n : ℕ) ζ.val).mp ζ.property)
  refine ⟨windingRootSystem ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  exact hj

end DiamondIntegral.Section5
