import «section 5».PuiseuxField
import «section 5».HahnCharacterActions
import «section 5».CompatibleRootSystems

/-! Actual automorphisms of the concrete Puiseux field from compatible
finite root systems. The action fixes the full Laurent base, not just t. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

/-- Every finite Laurent level embeds in the concrete Puiseux field. -/
def laurentToPuiseux {n : ℕ} (hn : 0 < n) : HahnSeries ℤ k →+* PuiseuxSeries k where
  toFun f := ⟨laurentToRational hn f, ⟨n, hn, f, rfl⟩⟩
  map_one' := Subtype.ext (map_one (laurentToRational hn))
  map_zero' := Subtype.ext (map_zero (laurentToRational hn))
  map_add' f g := Subtype.ext (map_add (laurentToRational hn) f g)
  map_mul' f g := Subtype.ext (map_mul (laurentToRational hn) f g)

/-- The actual unramified Laurent base inside the concrete Puiseux field. -/
abbrev puiseuxBaseSubfield (k : Type*) [Field k] : Subfield (PuiseuxSeries k) :=
  (laurentToPuiseux (k := k) (n := 1) (by omega)).fieldRange

theorem puiseuxCharacter_mem (χ : Multiplicative ℚ →* kˣ) (f : HahnSeries ℚ k)
    (hf : f ∈ puiseuxSubfield k) : hahnCharacterEquiv χ f ∈ puiseuxSubfield k := by
  obtain ⟨n, hn, hf⟩ := hf
  refine ⟨n, hn, ?_⟩
  rw [laurentToRational_range_iff] at hf ⊢
  exact Set.Subset.trans (by rw [show (hahnCharacterEquiv χ f).support = f.support from
    hahnCharacterTwist_support χ f]) hf

/-- Character twists restrict to actual ring automorphisms of Puiseux series. -/
def puiseuxCharacterEquiv (χ : Multiplicative ℚ →* kˣ) : PuiseuxSeries k ≃+* PuiseuxSeries k where
  toFun f := ⟨hahnCharacterEquiv χ f, puiseuxCharacter_mem χ f f.property⟩
  invFun f := ⟨hahnCharacterEquiv χ⁻¹ f, puiseuxCharacter_mem χ⁻¹ f f.property⟩
  left_inv f := Subtype.ext ((hahnCharacterEquiv χ).left_inv f)
  right_inv f := Subtype.ext ((hahnCharacterEquiv χ).right_inv f)
  map_add' f g := Subtype.ext (map_add (hahnCharacterEquiv χ) (f : HahnSeries ℚ k) (g : HahnSeries ℚ k))
  map_mul' f g := Subtype.ext (map_mul (hahnCharacterEquiv χ) (f : HahnSeries ℚ k) (g : HahnSeries ℚ k))

theorem puiseuxCharacter_fixes_base (χ : Multiplicative ℚ →* kˣ)
    (hχ : ∀ z : ℤ, χ (Multiplicative.ofAdd (z : ℚ)) = 1)
    (f : HahnSeries ℤ k) :
    puiseuxCharacterEquiv χ (laurentToPuiseux (n := 1) (by omega) f) =
      laurentToPuiseux (n := 1) (by omega) f := by
  apply Subtype.ext
  ext q
  change (χ (Multiplicative.ofAdd q) : k) * (laurentToRational (n := 1) (by omega) f).coeff q =
    (laurentToRational (n := 1) (by omega) f).coeff q
  by_cases hq : (laurentToRational (n := 1) (by omega) f).coeff q = 0
  · simp [hq]
  · obtain ⟨z, hz⟩ := (laurentToRational_range_iff (n := 1) (by omega) _).mp ⟨f, rfl⟩ hq
    have hz' : (z : ℚ) = q := by simpa [rationalExponentMap] using hz
    rw [← hz', hχ, Units.val_one, one_mul]

/-- A compatible finite system acts over the full original Laurent base. -/
def puiseuxRootSystemAction (η : CompatibleRoots k) :
    PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k where
  __ := puiseuxCharacterEquiv (compatibleRootCharacter η)
  commutes' b := by
    obtain ⟨f, hf⟩ := b.property
    change puiseuxCharacterEquiv (compatibleRootCharacter η) b.val = b.val
    rw [← hf]
    exact puiseuxCharacter_fixes_base (compatibleRootCharacter η)
      (compatibleRootCharacter_int η) f

/-- The global action preserves the actual rational-exponent valuation. -/
theorem puiseuxRootSystemAction_orderTop (η : CompatibleRoots k) (f : PuiseuxSeries k) :
    ((puiseuxRootSystemAction η f : PuiseuxSeries k) : HahnSeries ℚ k).orderTop =
      (f : HahnSeries ℚ k).orderTop :=
  hahnCharacterEquiv_orderTop (compatibleRootCharacter η) f


/-- A canonical root for the construction, kept outside the definability base. -/
def puiseuxRoot (n : ℕ+) : PuiseuxSeries k := laurentToPuiseux n.pos (single 1 1)

theorem puiseuxRoot_coe (n : ℕ+) :
    (puiseuxRoot (k := k) n : HahnSeries ℚ k) = single ((1 : ℚ) / (n : ℕ)) 1 := by
  change embDomain _ (single 1 1 : HahnSeries ℤ k) = _
  rw [embDomain_single]
  rfl

theorem puiseuxRoot_ne_zero (n : ℕ+) : puiseuxRoot (k := k) n ≠ 0 := by
  intro h
  have h := congrArg (fun f : PuiseuxSeries k => (f : HahnSeries ℚ k).coeff ((1 : ℚ) / (n : ℕ))) h
  simpa only [puiseuxRoot_coe, coeff_single_same, Subfield.coe_zero, coeff_zero, one_ne_zero] using h

/-- Constants embed in the original Laurent base and hence in Puiseux series. -/
def puiseuxConstant : k →+* PuiseuxSeries k :=
  (laurentToPuiseux (n := 1) (by omega)).comp C

theorem puiseuxConstant_coe (c : k) : (puiseuxConstant c : HahnSeries ℚ k) = C c := by
  change laurentToRational (n := 1) (by omega) (C c) = C c
  exact embDomainRingHom_C

/-- The distinguished base uniformizer, as an element of the full Laurent base. -/
def puiseuxBaseUniformizer : puiseuxBaseSubfield k :=
  ⟨puiseuxRoot 1, ⟨single 1 1, rfl⟩⟩

theorem puiseuxRoot_pow (n : ℕ+) : puiseuxRoot (k := k) n ^ (n : ℕ) =
    algebraMap (puiseuxBaseSubfield k) (PuiseuxSeries k) puiseuxBaseUniformizer := by
  apply Subtype.ext
  change (puiseuxRoot (k := k) n : HahnSeries ℚ k) ^ (n : ℕ) = (puiseuxRoot (k := k) 1 : HahnSeries ℚ k)
  rw [puiseuxRoot_coe, puiseuxRoot_coe, single_pow]
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hi : (n : ℕ) • ((1 : ℚ) / (n : ℕ)) = (1 : ℚ) / ((1 : ℕ+) : ℕ) := by
    simp only [nsmul_eq_mul]
    norm_num
  rw [hi, one_pow]

theorem puiseuxRoot_transition (n d : ℕ+) :
    puiseuxRoot (k := k) (n * d) ^ (d : ℕ) = puiseuxRoot n := by
  apply Subtype.ext
  change (puiseuxRoot (k := k) (n * d) : HahnSeries ℚ k) ^ (d : ℕ) = (puiseuxRoot (k := k) n : HahnSeries ℚ k)
  rw [puiseuxRoot_coe, puiseuxRoot_coe, single_pow]
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hd : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
  have hi : (d : ℕ) • ((1 : ℚ) / ((n * d : ℕ+) : ℕ)) = (1 : ℚ) / (n : ℕ) := by
    simp only [nsmul_eq_mul]
    simp only [PNat.mul_coe, Nat.cast_mul]
    field_simp
  rw [hi, one_pow]

/-- The global automorphism has exactly the prescribed finite root multiplier. -/
theorem puiseuxRootSystemAction_root (η : CompatibleRoots k) (n : ℕ+) :
    puiseuxRootSystemAction η (puiseuxRoot n) =
      puiseuxConstant ((η.val n : kˣ) : k) * puiseuxRoot n := by
  apply Subtype.ext
  change hahnCharacterTwist (compatibleRootCharacter η) (puiseuxRoot (k := k) n : HahnSeries ℚ k) = _
  rw [puiseuxRoot_coe]
  ext q
  change (compatibleRootCharacter η (Multiplicative.ofAdd q) : k) *
    (single ((1 : ℚ) / (n : ℕ)) 1 : HahnSeries ℚ k).coeff q = _
  change _ = ((puiseuxConstant ((η.val n : kˣ) : k) : HahnSeries ℚ k) *
    (puiseuxRoot (k := k) n : HahnSeries ℚ k)).coeff q
  rw [puiseuxConstant_coe, puiseuxRoot_coe]
  by_cases hq : q = (1 : ℚ) / (n : ℕ)
  · subst q
    rw [coeff_single_same]
    have hχ := compatibleRootCharacter_fraction η n 1
    simp only [Int.cast_one, zpow_one] at hχ
    rw [hχ]
    simp [coeff_single_mul, C]
  · rw [coeff_single_of_ne hq]
    simp only [mul_zero]
    rw [show C ((η.val n : kˣ) : k) = single (0 : ℚ) ((η.val n : kˣ) : k) from rfl,
      coeff_single_mul, sub_zero, coeff_single_of_ne hq, mul_zero]

theorem puiseuxRootSystemAction_injective :
    Function.Injective (puiseuxRootSystemAction (k := k)) := by
  intro η θ h
  apply Subtype.ext
  funext n
  have hroot := congrArg (fun σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k =>
    σ (puiseuxRoot (k := k) n)) h
  rw [puiseuxRootSystemAction_root η n, puiseuxRootSystemAction_root θ n] at hroot
  have hc := mul_right_cancel₀ (puiseuxRoot_ne_zero (k := k) n) hroot
  have hu := (puiseuxConstant (k := k)).injective hc
  exact Units.ext hu

end DiamondIntegral.Section5
