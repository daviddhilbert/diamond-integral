import «section 5».LaurentKummerBasis
import «section 5».HahnEmbeddings

/-! A concrete Puiseux field inside rational-exponent Hahn series.
Membership means an actual Laurent series at a finite denominator. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

def rationalExponentMap (n : ℕ) : ℤ →+ ℚ where
  toFun z := (z : ℚ) / n
  map_zero' := zero_div _
  map_add' _ _ := by simp [add_div]

theorem rationalExponentMap_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (rationalExponentMap n) := by
  intro x y h
  change (x : ℚ) / n = (y : ℚ) / n at h
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  exact_mod_cast (div_left_inj' hn').mp h

theorem rationalExponentMap_le {n : ℕ} (hn : 0 < n) (x y : ℤ) :
    rationalExponentMap n x ≤ rationalExponentMap n y ↔ x ≤ y := by
  change (x : ℚ) / n ≤ (y : ℚ) / n ↔ x ≤ y
  rw [div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
  exact Int.cast_le

/-- The finite level k((t^(1/n))) in a common rational-exponent Hahn field. -/
def laurentToRational {n : ℕ} (hn : 0 < n) : HahnSeries ℤ k →+* HahnSeries ℚ k :=
  embDomainRingHom (rationalExponentMap n) (rationalExponentMap_injective hn)
    (rationalExponentMap_le hn)

/-- Pull rational coefficients back to one finite denominator. -/
def rationalLaurentPart {n : ℕ} (hn : 0 < n) (f : HahnSeries ℚ k) : HahnSeries ℤ k where
  coeff z := f.coeff (rationalExponentMap n z)
  isPWO_support' := by
    rw [Set.isPWO_iff_exists_monotone_subseq]
    intro g hg
    obtain ⟨e, he⟩ := f.isPWO_support.exists_monotone_subseq
      (f := fun i => rationalExponentMap n (g i)) hg
    exact ⟨e, fun _ _ hab => (rationalExponentMap_le hn _ _).mp (he hab)⟩

theorem laurentToRational_range_iff {n : ℕ} (hn : 0 < n) (f : HahnSeries ℚ k) :
    f ∈ (laurentToRational (k := k) hn).fieldRange ↔
      f.support ⊆ Set.range (rationalExponentMap n) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact Set.Subset.trans support_embDomain_subset (Set.image_subset_range _ _)
  · intro hf
    refine ⟨rationalLaurentPart hn f, ?_⟩
    ext q
    by_cases hq : q ∈ Set.range (rationalExponentMap n)
    · obtain ⟨z, rfl⟩ := hq
      exact embDomain_coeff
    · have hzero : f.coeff q = 0 := by
        by_contra h
        exact hq (hf h)
      rw [hzero]
      exact embDomain_of_notMem_range hq

theorem laurentToRational_level_mono {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hdiv : n ∣ m) :
    (laurentToRational (k := k) hn).fieldRange ≤ (laurentToRational (k := k) hm).fieldRange := by
  intro f hf
  rw [laurentToRational_range_iff] at hf ⊢
  intro q hq
  obtain ⟨z, rfl⟩ := hf hq
  obtain ⟨d, hd⟩ := hdiv
  refine ⟨(d : ℤ) * z, ?_⟩
  dsimp [rationalExponentMap]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd' : (m : ℚ) = (n : ℚ) * d := by exact_mod_cast hd
  push_cast
  apply (div_eq_div_iff hm' hn').mpr
  rw [hd']
  ring

/-- Puiseux series are exactly the union of all finite Laurent levels. -/
def puiseuxSubfield (k : Type*) [Field k] : Subfield (HahnSeries ℚ k) where
  carrier := {f | ∃ (n : ℕ) (hn : 0 < n), f ∈ (laurentToRational (k := k) hn).fieldRange}
  zero_mem' := ⟨1, by omega, zero_mem _⟩
  one_mem' := ⟨1, by omega, one_mem _⟩
  add_mem' := by
    rintro f g ⟨n, hn, hf⟩ ⟨m, hm, hg⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    exact add_mem (laurentToRational_level_mono hn (Nat.mul_pos hn hm) (dvd_mul_right n m) hf)
      (laurentToRational_level_mono hm (Nat.mul_pos hn hm) (dvd_mul_left m n) hg)
  mul_mem' := by
    rintro f g ⟨n, hn, hf⟩ ⟨m, hm, hg⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    exact mul_mem (laurentToRational_level_mono hn (Nat.mul_pos hn hm) (dvd_mul_right n m) hf)
      (laurentToRational_level_mono hm (Nat.mul_pos hn hm) (dvd_mul_left m n) hg)
  neg_mem' := by
    rintro f ⟨n, hn, hf⟩
    exact ⟨n, hn, neg_mem hf⟩
  inv_mem' := by
    rintro f ⟨n, hn, hf⟩
    exact ⟨n, hn, inv_mem hf⟩

abbrev PuiseuxSeries (k : Type*) [Field k] := ↥(puiseuxSubfield k)

theorem puiseuxSeries_finite_level (f : PuiseuxSeries k) :
    ∃ (n : ℕ) (hn : 0 < n) (g : HahnSeries ℤ k), laurentToRational hn g = (f : HahnSeries ℚ k) :=
  f.property


/-- At level n, the substitution t = tau^n recovers the original base. -/
theorem laurentToRational_scale {n : ℕ} (hn : 0 < n) (f : HahnSeries ℤ k) :
    laurentToRational hn (laurentScale hn f) = laurentToRational (n := 1) (by omega) f := by
  change embDomain _ (embDomain _ f) = embDomain _ f
  rw [hahnEmbDomain_comp]
  congr 1
  ext z
  change ((n : ℤ) * z : ℤ) / (n : ℚ) = (z : ℚ) / (1 : ℕ)
  push_cast
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end DiamondIntegral.Section5
