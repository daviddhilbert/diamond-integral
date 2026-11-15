import «section 5».KummerRootCharacters
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Compatible finite roots of unity and characters of Q trivial on Z.
Compatibility is imposed at every positive pair (n,d), at levels n and n*d. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
variable {k : Type*} [Field k]

/-- The inverse system of finite roots, as a subgroup of the product of unit groups. -/
def compatibleRootSubgroup (k : Type*) [Field k] : Subgroup (ℕ+ → kˣ) where
  carrier := {η | (∀ n : ℕ+, η n ^ (n : ℕ) = 1) ∧
    ∀ n d : ℕ+, η (n * d) ^ (d : ℕ) = η n}
  one_mem' := by simp
  mul_mem' := by
    rintro η θ ⟨hη, hcη⟩ ⟨hθ, hcθ⟩
    constructor
    · intro n
      simp only [Pi.mul_apply, mul_pow, hη, hθ, mul_one]
    · intro n d
      simp only [Pi.mul_apply, mul_pow, hcη, hcθ]
  inv_mem' := by
    rintro η ⟨hη, hcη⟩
    constructor
    · intro n
      simp only [Pi.inv_apply, inv_pow, hη, inv_one]
    · intro n d
      simp only [Pi.inv_apply, inv_pow, hcη]

abbrev CompatibleRoots (k : Type*) [Field k] := ↥(compatibleRootSubgroup k)

/-- The value at a rational number, initially using its canonical denominator. -/
def compatibleRootValue (η : CompatibleRoots k) (q : ℚ) : kˣ :=
  η.val ⟨q.den, q.den_pos⟩ ^ q.num

/-- The canonical value agrees with every representation z/n. -/
theorem compatibleRootValue_fraction (η : CompatibleRoots k) (n : ℕ+) (z : ℤ) :
    compatibleRootValue η ((z : ℚ) / (n : ℕ)) = η.val n ^ z := by
  let q : ℚ := (z : ℚ) / (n : ℕ)
  let d : ℕ+ := ⟨q.den, q.den_pos⟩
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  have he : (q.num : ℚ) / (d : ℕ) = (z : ℚ) / (n : ℕ) := Rat.num_div_den q
  have he' : q.num * (n : ℕ) = (d : ℕ) * z := by
    have h := (div_eq_div_iff hd hn).mp he
    exact_mod_cast h.trans (mul_comm _ _)
  have hdn := η.property.2 d n
  have hnd := η.property.2 n d
  rw [mul_comm n d] at hnd
  change η.val d ^ q.num = η.val n ^ z
  rw [← hdn, ← hnd]
  simp only [← zpow_natCast, ← zpow_mul]
  rw [mul_comm (n : ℤ) q.num, he']


/-- Every compatible system determines a genuine character of Q. -/
def compatibleRootCharacter (η : CompatibleRoots k) : Multiplicative ℚ →* kˣ where
  toFun q := compatibleRootValue η q.toAdd
  map_one' := by
    change compatibleRootValue η 0 = 1
    have h := compatibleRootValue_fraction η (1 : ℕ+) (0 : ℤ)
    simpa using h
  map_mul' x y := by
    let q := x.toAdd
    let r := y.toAdd
    let n : ℕ+ := ⟨q.den * r.den, Nat.mul_pos q.den_pos r.den_pos⟩
    let a : ℤ := q.num * r.den
    let b : ℤ := r.num * q.den
    have hq : (a : ℚ) / (n : ℕ) = q := by
      change ((q.num * (r.den : ℤ) : ℤ) : ℚ) / (q.den * r.den : ℕ) = q
      push_cast
      calc
        _ = (q.num : ℚ) / q.den := by
          field_simp [q.den_nz, r.den_nz]
        _ = q := Rat.num_div_den q
    have hr : (b : ℚ) / (n : ℕ) = r := by
      change ((r.num * (q.den : ℤ) : ℤ) : ℚ) / (q.den * r.den : ℕ) = r
      push_cast
      calc
        _ = (r.num : ℚ) / r.den := by
          field_simp [q.den_nz, r.den_nz]
        _ = r := Rat.num_div_den r
    change compatibleRootValue η (q + r) = compatibleRootValue η q * compatibleRootValue η r
    rw [← hq, ← hr, ← add_div, ← Int.cast_add, compatibleRootValue_fraction,
      compatibleRootValue_fraction, compatibleRootValue_fraction, zpow_add]

theorem compatibleRootCharacter_fraction (η : CompatibleRoots k) (n : ℕ+) (z : ℤ) :
    compatibleRootCharacter η (Multiplicative.ofAdd ((z : ℚ) / (n : ℕ))) = η.val n ^ z :=
  compatibleRootValue_fraction η n z

/-- The character fixes all integral exponents, hence the original base. -/
theorem compatibleRootCharacter_int (η : CompatibleRoots k) (z : ℤ) :
    compatibleRootCharacter η (Multiplicative.ofAdd (z : ℚ)) = 1 := by
  have h1 : η.val 1 = 1 := by simpa using η.property.1 1
  have h := compatibleRootCharacter_fraction η (1 : ℕ+) z
  simpa only [PNat.val_ofNat, Nat.cast_one, div_one, h1, one_zpow] using h


/-- Read a compatible finite system from any rational character trivial at 1. -/
def rationalCharacterSystem (χ : Multiplicative ℚ →* kˣ)
    (hχ : χ (Multiplicative.ofAdd 1) = 1) : CompatibleRoots k := by
  refine ⟨fun n => χ (Multiplicative.ofAdd ((1 : ℚ) / (n : ℕ))), ?_, ?_⟩
  · intro n
    rw [← map_pow, ← ofAdd_nsmul]
    have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hi : (n : ℕ) • ((1 : ℚ) / (n : ℕ)) = 1 := by
      simp [nsmul_eq_mul, hn]
    rw [hi]
    exact hχ
  · intro n d
    rw [← map_pow, ← ofAdd_nsmul]
    congr 1
    simp only [nsmul_eq_mul, PNat.mul_coe, Nat.cast_mul]
    have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hd : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
    field_simp

/-- Passing to finite roots and back recovers the entire rational character. -/
theorem compatibleRootCharacter_system (χ : Multiplicative ℚ →* kˣ)
    (hχ : χ (Multiplicative.ofAdd 1) = 1) :
    compatibleRootCharacter (rationalCharacterSystem χ hχ) = χ := by
  apply MonoidHom.ext
  intro q
  change χ (Multiplicative.ofAdd ((1 : ℚ) / q.toAdd.den)) ^ q.toAdd.num = χ q
  rw [← map_zpow, ← ofAdd_zsmul]
  congr 1
  change (q.toAdd.num : ℚ) * ((1 : ℚ) / q.toAdd.den) = q.toAdd
  rw [mul_one_div, Rat.num_div_den]

end DiamondIntegral.Section5
