import «section 5».CompatibleRootSystems

/-! Automorphisms of rational leading-term coordinates over integral values
and all constants. No order-preservation hypothesis is needed: fixing the
integral values forces every rational value to be fixed. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
variable {k : Type*} [Field k]

abbrev RationalRVUnits (k : Type*) [Field k] := Multiplicative ℚ × kˣ

/-- The coefficient character of a leading-term group automorphism. -/
def rationalRVCharacter (φ : RationalRVUnits k ≃* RationalRVUnits k) :
    Multiplicative ℚ →* kˣ where
  toFun q := (φ (q, 1)).2
  map_one' := by
    change (φ (1 : RationalRVUnits k)).2 = 1
    rw [map_one]
    rfl
  map_mul' q r := by
    simpa using congrArg Prod.snd (φ.map_mul (q, 1) (r, 1))

theorem rationalRVAutomorphism_value
    (φ : RationalRVUnits k ≃* RationalRVUnits k)
    (hfix : ∀ (z : ℤ) (c : kˣ), φ (Multiplicative.ofAdd (z : ℚ), c) =
      (Multiplicative.ofAdd (z : ℚ), c)) (q : ℚ) :
    (φ (Multiplicative.ofAdd q, 1)).1 = Multiplicative.ofAdd q := by
  have hroot : (Multiplicative.ofAdd q, (1 : kˣ)) ^ q.den =
      (Multiplicative.ofAdd (q.num : ℚ), 1) := by
    apply Prod.ext
    · change (Multiplicative.ofAdd q) ^ q.den = Multiplicative.ofAdd (q.num : ℚ)
      rw [← ofAdd_nsmul]
      congr 1
      simpa only [nsmul_eq_mul, mul_comm] using Rat.mul_den_eq_num q
    · simp
  have hp : φ (Multiplicative.ofAdd q, 1) ^ q.den =
      (Multiplicative.ofAdd (q.num : ℚ), 1) := by
    rw [← map_pow, hroot, hfix]
  have hv := congrArg (fun u : RationalRVUnits k => u.1.toAdd) hp
  change ((φ (Multiplicative.ofAdd q, 1)).1 ^ q.den).toAdd = (q.num : ℚ) at hv
  rw [toAdd_pow, nsmul_eq_mul] at hv
  apply Multiplicative.toAdd.injective
  change (φ (Multiplicative.ofAdd q, 1)).1.toAdd = q
  have hn : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq := Rat.mul_den_eq_num q
  nlinarith

theorem rationalRVAutomorphism_formula
    (φ : RationalRVUnits k ≃* RationalRVUnits k)
    (hfix : ∀ (z : ℤ) (c : kˣ), φ (Multiplicative.ofAdd (z : ℚ), c) =
      (Multiplicative.ofAdd (z : ℚ), c)) (q : ℚ) (c : kˣ) :
    φ (Multiplicative.ofAdd q, c) =
      (Multiplicative.ofAdd q, rationalRVCharacter φ (Multiplicative.ofAdd q) * c) := by
  have hc : φ (1, c) = (1, c) := by simpa using hfix 0 c
  calc
    φ (Multiplicative.ofAdd q, c) = φ (Multiplicative.ofAdd q, 1) * (1, c) := by
      rw [← hc, ← map_mul]
      simp
    _ = _ := by
      apply Prod.ext
      · simpa using rationalRVAutomorphism_value φ hfix q
      · rfl

/-- Every such automorphism comes from a compatible system of finite roots. -/
theorem rationalRVAutomorphism_system
    (φ : RationalRVUnits k ≃* RationalRVUnits k)
    (hfix : ∀ (z : ℤ) (c : kˣ), φ (Multiplicative.ofAdd (z : ℚ), c) =
      (Multiplicative.ofAdd (z : ℚ), c)) :
    ∃ η : CompatibleRoots k, ∀ (q : ℚ) (c : kˣ),
      φ (Multiplicative.ofAdd q, c) =
        (Multiplicative.ofAdd q, compatibleRootCharacter η (Multiplicative.ofAdd q) * c) := by
  have hχ : rationalRVCharacter φ (Multiplicative.ofAdd 1) = 1 := by
    have h := congrArg Prod.snd (hfix 1 1)
    exact h
  refine ⟨rationalCharacterSystem (rationalRVCharacter φ) hχ, ?_⟩
  intro q c
  rw [compatibleRootCharacter_system]
  exact rationalRVAutomorphism_formula φ hfix q c

/-- Finite root values uniquely determine that system. -/
theorem rationalRVSystem_unique (η θ : CompatibleRoots k)
    (h : ∀ q : ℚ, compatibleRootCharacter η (Multiplicative.ofAdd q) =
      compatibleRootCharacter θ (Multiplicative.ofAdd q)) : η = θ := by
  apply Subtype.ext
  funext n
  have hn := h ((1 : ℚ) / (n : ℕ))
  have hη := compatibleRootCharacter_fraction η n 1
  have hθ := compatibleRootCharacter_fraction θ n 1
  simpa only [Int.cast_one, zpow_one] using hη.symm.trans (hn.trans hθ)

end DiamondIntegral.Section5
