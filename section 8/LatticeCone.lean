import «section 8».RationalSeries
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-! The generating series of a cone with unique decompositions.

Let `E` be an abelian group (a lattice), `P` a finite subset, and `v j` finitely
many generators such that every sum `p + ∑ n_j v_j` (`p ∈ P`, `n_j ∈ ℕ`)
determines `p` and `n`. Let `deg, L : E → ℤ` be additive with `deg (v j) > 0`
and `deg ≥ 0` on `P`. The series

  `Z = ∑_x A^(L x) T^(deg x)`,  `x` running over these sums,

satisfies `Z · ∏_j (1 − A^(L v_j) T^(deg v_j)) = ∑_{p ∈ P} A^(L p) T^(deg p)`.
If moreover `deg p ≤ ∑_j deg (v j)` on `P` with equality only at `∑_j v_j ∈ P`,
then `Z` has limit `(−1)^(number of generators)` at infinity.

This is the generating function of the lattice points of a simplicial cone
(Step 2 of the direct proof of Hrushovski–Loeser, Lemma 8.5.2). The file uses
Mathlib only. -/

set_option autoImplicit false

open Polynomial

namespace DiamondIntegral.Section8.LatticeCone

open RationalSeries

variable {R : Type*} [CommRing R] (A : Rˣ)
variable {E : Type*} [AddCommGroup E] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (P : Finset E) (v : ι → E) (deg L : E →+ ℤ)

/-- The sums `p + ∑ n_j v_j` with `p ∈ P` and `n` supported in `S`. -/
def coneSet (S : Finset ι) : Set E :=
  {x | ∃ p ∈ P, ∃ n : ι → ℕ, (∀ j, j ∉ S → n j = 0) ∧ x = p + ∑ j, n j • v j}

/-- The points of `coneSet` of a given degree. -/
def level (S : Finset ι) (z : ℤ) : Set E := {x | x ∈ coneSet P v S ∧ deg x = z}

/-- The coefficient `A^(L x)`. -/
def weight (x : E) : R := ((A ^ L x : Rˣ) : R)

/-- The series `∑_x A^(L x) T^(deg x)` over `coneSet P v S`. -/
noncomputable def series (S : Finset ι) : PowerSeries R :=
  PowerSeries.mk fun m : ℕ => ∑ᶠ x ∈ level P v deg S (m : ℤ), weight A L x

/-- The numerator `∑_{p ∈ P} A^(L p) T^(deg p)`. -/
noncomputable def numerator : R[X] := ∑ p ∈ P, C (weight A L p) * X ^ (deg p).toNat

/-- The denominator `∏_j (1 − A^(L v_j) T^(deg v_j))`. -/
noncomputable def denominator (S : Finset ι) : R[X] :=
  ∏ j ∈ S, daggerFactor A (L (v j)) (deg (v j)).toNat

theorem weight_add (x y : E) : weight A L (x + y) = weight A L x * weight A L y := by
  simp [weight, map_add, zpow_add]

omit [Fintype ι] in
theorem weight_sum (s : Finset ι) (f : ι → E) :
    weight A L (∑ j ∈ s, f j) = ∏ j ∈ s, weight A L (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, weight_add, ih]

omit [DecidableEq ι] in
theorem deg_param (p : E) (n : ι → ℕ) :
    deg (p + ∑ j, n j • v j) = deg p + ∑ j, (n j : ℤ) * deg (v j) := by
  simp [map_add, map_sum, map_nsmul]

theorem sum_add_single (n : ι → ℕ) (j : ι) :
    ∑ i, (n + Pi.single j 1 : ι → ℕ) i • v i = ∑ i, n i • v i + v j := by
  simp [add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]

section hypotheses

variable (hinj : ∀ p ∈ P, ∀ p' ∈ P, ∀ n n' : ι → ℕ,
  p + ∑ j, n j • v j = p' + ∑ j, n' j • v j → p = p' ∧ n = n')
variable (hv : ∀ j, 0 < deg (v j)) (hP : ∀ p ∈ P, 0 ≤ deg p)

include hv hP in
omit [DecidableEq ι] in
theorem deg_nonneg_of_mem {S : Finset ι} {x : E} (hx : x ∈ coneSet P v S) : 0 ≤ deg x := by
  obtain ⟨p, hp, n, -, rfl⟩ := hx
  rw [deg_param]
  have := hP p hp
  have : 0 ≤ ∑ j, (n j : ℤ) * deg (v j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Int.natCast_nonneg _) (hv j).le
  omega

include hv hP in
omit [DecidableEq ι] in
theorem level_eq_empty {S : Finset ι} {z : ℤ} (hz : z < 0) : level P v deg S z = ∅ := by
  ext x
  simp only [level, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hd
  have := deg_nonneg_of_mem P v deg hv hP hx
  omega

include hv hP in
theorem level_finite (S : Finset ι) (z : ℤ) : (level P v deg S z).Finite := by
  classical
  refine ((P ×ˢ Fintype.piFinset fun _ : ι => Finset.range (z.toNat + 1)).image
    (fun q : E × (ι → ℕ) => q.1 + ∑ j, q.2 j • v j)).finite_toSet.subset ?_
  rintro x ⟨⟨p, hp, n, -, rfl⟩, hz⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
    Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨(p, n), ⟨hp, fun j => ?_⟩, rfl⟩
  show n j < z.toNat + 1
  rw [deg_param] at hz
  have h1 : (n j : ℤ) ≤ (n j : ℤ) * deg (v j) :=
    le_mul_of_one_le_right (Int.natCast_nonneg _) (hv j)
  have h2 : (n j : ℤ) * deg (v j) ≤ ∑ i, (n i : ℤ) * deg (v i) :=
    Finset.single_le_sum (f := fun i => (n i : ℤ) * deg (v i))
      (fun i _ => mul_nonneg (Int.natCast_nonneg _) (hv i).le) (Finset.mem_univ j)
  have := hP p hp
  omega

omit [DecidableEq ι] in
theorem coneSet_mono {S T : Finset ι} (h : S ⊆ T) : coneSet P v S ⊆ coneSet P v T := by
  rintro x ⟨p, hp, n, hn, rfl⟩
  exact ⟨p, hp, n, fun j hj => hn j fun hjS => hj (h hjS), rfl⟩

theorem level_insert {S : Finset ι} {j : ι} (z : ℤ) :
    level P v deg (insert j S) z =
      level P v deg S z ∪ (fun x => x + v j) '' level P v deg (insert j S) (z - deg (v j)) := by
  ext x
  constructor
  · rintro ⟨⟨p, hp, n, hn, rfl⟩, hz⟩
    by_cases h0 : n j = 0
    · left
      refine ⟨⟨p, hp, n, fun i hi => ?_, rfl⟩, hz⟩
      by_cases hij : i = j
      · rw [hij]; exact h0
      · exact hn i (by simp [hij, hi])
    · right
      let n' : ι → ℕ := fun i => if i = j then n j - 1 else n i
      have hn' : n = n' + Pi.single j 1 := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [n']; omega
        · simp [n', hij]
      have hx : p + ∑ i, n i • v i = (p + ∑ i, n' i • v i) + v j := by
        rw [hn', sum_add_single, add_assoc]
      refine ⟨p + ∑ i, n' i • v i, ⟨⟨p, hp, n', fun i hi => ?_, rfl⟩, ?_⟩, hx.symm⟩
      · have hij : i ≠ j := fun h => hi (by simp [h])
        simp only [n', hij, ↓reduceIte]
        exact hn i hi
      · rw [hx, map_add] at hz
        omega
  · rintro (⟨hx, hz⟩ | ⟨y, ⟨⟨p, hp, n, hn, rfl⟩, hz⟩, rfl⟩)
    · exact ⟨coneSet_mono P v (Finset.subset_insert j S) hx, hz⟩
    · refine ⟨⟨p, hp, n + Pi.single j 1, fun i hi => ?_, ?_⟩, ?_⟩
      · have hij : i ≠ j := fun h => hi (by simp [h])
        simp [hn i hi, hij]
      · rw [sum_add_single]; exact add_assoc _ _ _
      · rw [map_add, hz]; ring

include hinj in
theorem level_insert_disjoint {S : Finset ι} {j : ι} (hj : j ∉ S) (z : ℤ) :
    Disjoint (level P v deg S z)
      ((fun x => x + v j) '' level P v deg (insert j S) (z - deg (v j))) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨p, hp, n, hn, rfl⟩, -⟩ ⟨y, ⟨⟨p', hp', n', -, rfl⟩, -⟩, hy⟩
  have hy' : p' + ∑ i, (n' + Pi.single j 1 : ι → ℕ) i • v i = p + ∑ i, n i • v i := by
    rw [sum_add_single, ← add_assoc]; exact hy
  have h := (hinj p' hp' p hp _ _ hy').2
  have h1 := congrFun h j
  have h2 := hn j hj
  simp at h1
  omega

include hinj hv hP in
theorem finsum_level_insert {S : Finset ι} {j : ι} (hj : j ∉ S) (z : ℤ) :
    ∑ᶠ x ∈ level P v deg (insert j S) z, weight A L x =
      ∑ᶠ x ∈ level P v deg S z, weight A L x +
        weight A L (v j) * ∑ᶠ x ∈ level P v deg (insert j S) (z - deg (v j)), weight A L x := by
  rw [level_insert P v deg z,
    finsum_mem_union (level_insert_disjoint P v deg hinj hj z) (level_finite P v deg hv hP S z)
      ((level_finite P v deg hv hP _ _).image _),
    finsum_mem_image (add_left_injective (v j)).injOn,
    mul_finsum_mem' _ _ (level_finite P v deg hv hP _ _)]
  congr 1
  exact finsum_mem_congr rfl fun x _ => by rw [weight_add, mul_comm]

theorem coeff_mul_one_sub (Z : PowerSeries R) (u : R) (b m : ℕ) :
    PowerSeries.coeff m (Z * (1 - PowerSeries.C u * PowerSeries.X ^ b)) =
      PowerSeries.coeff m Z - u * (if b ≤ m then PowerSeries.coeff (m - b) Z else 0) := by
  rw [mul_sub, mul_one, map_sub, mul_left_comm, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow']

include hinj hv hP in
theorem series_insert_mul {S : Finset ι} {j : ι} (hj : j ∉ S) :
    series A P v deg L (insert j S) *
        ((daggerFactor A (L (v j)) (deg (v j)).toNat : R[X]) : PowerSeries R) =
      series A P v deg L S := by
  have hcoe : ((daggerFactor A (L (v j)) (deg (v j)).toNat : R[X]) : PowerSeries R) =
      1 - PowerSeries.C (weight A L (v j)) * PowerSeries.X ^ (deg (v j)).toNat := by
    simp [daggerFactor, weight]
  have hb : ((deg (v j)).toNat : ℤ) = deg (v j) := Int.toNat_of_nonneg (hv j).le
  ext m
  rw [hcoe, coeff_mul_one_sub]
  simp only [series, PowerSeries.coeff_mk]
  rw [finsum_level_insert A P v deg L hinj hv hP hj]
  by_cases h : (deg (v j)).toNat ≤ m
  · have hz : (m : ℤ) - deg (v j) = ((m - (deg (v j)).toNat : ℕ) : ℤ) := by omega
    simp only [h, ↓reduceIte, hz]
    ring
  · have hz : (m : ℤ) - deg (v j) < 0 := by omega
    simp only [h, ↓reduceIte]
    rw [level_eq_empty P v deg hv hP hz, finsum_mem_empty]
    ring

include hP in
omit [DecidableEq ι] in
theorem series_empty : series A P v deg L ∅ = ((numerator A P deg L : R[X]) : PowerSeries R) := by
  classical
  ext m
  have hlev : level P v deg ∅ (m : ℤ) = ↑(P.filter fun p => deg p = (m : ℤ)) := by
    ext x
    simp only [level, coneSet, Set.mem_ofPred_eq, Finset.coe_filter]
    constructor
    · rintro ⟨⟨p, hp, n, hn, rfl⟩, hz⟩
      have h0 : n = 0 := funext fun j => hn j (Finset.notMem_empty j)
      subst h0
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at hz ⊢
      exact ⟨hp, hz⟩
    · rintro ⟨hp, hz⟩
      exact ⟨⟨x, hp, 0, fun _ _ => rfl, by simp⟩, hz⟩
  simp only [series, PowerSeries.coeff_mk, numerator, Polynomial.coeff_coe, finsetSum_coeff,
    coeff_C_mul_X_pow]
  rw [hlev, finsum_mem_coe_finset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  have := hP p hp
  have hiff : deg p = (m : ℤ) ↔ m = (deg p).toNat := by omega
  simp only [hiff]

include hinj hv hP in
/-- `Z_S · ∏_{j ∈ S} (1 − A^(L v_j) T^(deg v_j))` is the numerator. -/
theorem series_mul_denominator (S : Finset ι) :
    series A P v deg L S * ((denominator A v deg L S : R[X]) : PowerSeries R) =
      ((numerator A P deg L : R[X]) : PowerSeries R) := by
  induction S using Finset.induction_on with
  | empty => simp [denominator, series_empty A P v deg L hP]
  | insert j S hj ih =>
    rw [denominator, Finset.prod_insert hj, Polynomial.coe_mul, ← mul_assoc,
      series_insert_mul A P v deg L hinj hv hP hj]
    exact ih

omit [Fintype ι] [DecidableEq ι] in
theorem denominator_mem (S : Finset ι) (hv : ∀ j, 0 < deg (v j)) :
    denominator A v deg L S ∈ daggerDenominators A :=
  Submonoid.prod_mem _ fun j _ =>
    daggerFactor_mem A _ (by have := hv j; omega)

include hv in
omit [Fintype ι] [DecidableEq ι] in
theorem natDegree_denominator [Nontrivial R] (S : Finset ι) :
    (denominator A v deg L S).natDegree = ∑ j ∈ S, (deg (v j)).toNat := by
  have hpos : ∀ j, 0 < (deg (v j)).toNat := fun j => by have := hv j; omega
  have hne : ∏ j ∈ S, (daggerFactor A (L (v j)) (deg (v j)).toNat).leadingCoeff ≠ 0 := by
    refine IsUnit.ne_zero ?_
    rw [Finset.prod_congr rfl fun j _ => leadingCoeff_daggerFactor A (L (v j)) (hpos j)]
    have hcoe : ∏ j ∈ S, -((A ^ L (v j) : Rˣ) : R) = ((∏ j ∈ S, -(A ^ L (v j)) : Rˣ) : R) := by
      simp [Units.coe_prod]
    rw [hcoe]
    exact Units.isUnit _
  rw [denominator, natDegree_prod' _ _ hne]
  exact Finset.sum_congr rfl fun j _ => natDegree_daggerFactor A _ (hpos j)

include hv in
omit [Fintype ι] in
theorem leadingCoeff_denominator [Nontrivial R] (S : Finset ι) :
    (denominator A v deg L S).leadingCoeff = (-1) ^ S.card * weight A L (∑ j ∈ S, v j) := by
  have hpos : ∀ j, 0 < (deg (v j)).toNat := fun j => by have := hv j; omega
  have hne : ∏ j ∈ S, (daggerFactor A (L (v j)) (deg (v j)).toNat).leadingCoeff ≠ 0 := by
    refine IsUnit.ne_zero ?_
    rw [Finset.prod_congr rfl fun j _ => leadingCoeff_daggerFactor A (L (v j)) (hpos j)]
    have hcoe : ∏ j ∈ S, -((A ^ L (v j) : Rˣ) : R) = ((∏ j ∈ S, -(A ^ L (v j)) : Rˣ) : R) := by
      simp [Units.coe_prod]
    rw [hcoe]
    exact Units.isUnit _
  rw [denominator, leadingCoeff_prod' _ _ hne,
    Finset.prod_congr rfl fun j _ => leadingCoeff_daggerFactor A (L (v j)) (hpos j),
    Finset.prod_neg, weight_sum]
  rfl

theorem natDegree_numerator_le (M : ℕ) (hM : ∀ p ∈ P, deg p ≤ M) :
    (numerator A P deg L).natDegree ≤ M :=
  natDegree_sum_le_of_forall_le _ _ fun p hp =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := hM p hp; omega)

include hP in
theorem coeff_numerator_top (M : ℕ) (q : E) (hq : q ∈ P) (hqM : deg q = M)
    (htop : ∀ p ∈ P, deg p = M → p = q) :
    (numerator A P deg L).coeff M = weight A L q := by
  classical
  rw [numerator, finsetSum_coeff, Finset.sum_eq_single q]
  · rw [coeff_C_mul_X_pow]
    simp [hqM]
  · intro p hp hpq
    rw [coeff_C_mul_X_pow]
    have hne : M ≠ (deg p).toNat := fun h =>
      hpq (htop p hp (by have := hP p hp; omega))
    simp [hne]
  · intro h
    exact absurd hq h

include hinj hv hP in
/-- The series of the whole cone has limit `(−1)^(number of generators)`. -/
theorem hasLimit_series (hmem : ∑ j, v j ∈ P) (hM : ∀ p ∈ P, deg p ≤ deg (∑ j, v j))
    (htop : ∀ p ∈ P, deg p = deg (∑ j, v j) → p = ∑ j, v j) :
    HasLimit A (series A P v deg L Finset.univ) ((-1) ^ Fintype.card ι) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact hasLimit_of_subsingleton A _ _
  have hdegsum : deg (∑ j, v j) = ((∑ j, (deg (v j)).toNat : ℕ) : ℤ) := by
    rw [map_sum, Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => (Int.toNat_of_nonneg (hv j).le).symm
  refine hasLimit_of_fraction A (P := numerator A P deg L)
    (denominator_mem A v deg L Finset.univ hv) ?_ ?_ ?_
  · rw [mul_comm]
    exact series_mul_denominator A P v deg L hinj hv hP Finset.univ
  · rw [natDegree_denominator A v deg L hv]
    exact natDegree_numerator_le A P deg L _ fun p hp => hdegsum ▸ hM p hp
  · rw [natDegree_denominator A v deg L hv,
      coeff_numerator_top A P deg L hP _ (∑ j, v j) hmem hdegsum
        (fun p hp h => htop p hp (hdegsum ▸ h)),
      leadingCoeff_denominator A v deg L hv, Finset.card_univ, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    simp

end hypotheses

end DiamondIntegral.Section8.LatticeCone
