import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.Field.Subfield.Basic

/-! Grouping Laurent exponents modulo a positive integer. These are actual
Hahn/Laurent series, not a postulated finite-dimensional extension. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
open scoped BigOperators
variable {k : Type*} [Field k]

/-- Exponent multiplication by n, used for the substitution t = tau^n. -/
def laurentExponentMap (n : ℕ) : ℤ →+ ℤ where
  toFun z := (n : ℤ) * z
  map_zero' := mul_zero _
  map_add' _ _ := mul_add _ _ _

theorem laurentExponentMap_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (laurentExponentMap n) := by
  intro x y h
  change (n : ℤ) * x = (n : ℤ) * y at h
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') h

theorem laurentExponentMap_le {n : ℕ} (hn : 0 < n) (x y : ℤ) :
    laurentExponentMap n x ≤ laurentExponentMap n y ↔ x ≤ y := by
  change (n : ℤ) * x ≤ (n : ℤ) * y ↔ x ≤ y
  exact mul_le_mul_iff_right₀ (by exact_mod_cast hn)

/-- The actual embedding k((t)) into k((tau)) with t mapped to tau^n. -/
def laurentScale {n : ℕ} (hn : 0 < n) : HahnSeries ℤ k →+* HahnSeries ℤ k :=
  embDomainRingHom (laurentExponentMap n) (laurentExponentMap_injective hn)
    (laurentExponentMap_le hn)

theorem laurentScale_coeff {n : ℕ} (hn : 0 < n) (f : HahnSeries ℤ k) (q : ℤ) :
    (laurentScale hn f).coeff ((n : ℤ) * q) = f.coeff q :=
  embDomain_coeff

theorem laurentScale_coeff_of_not_dvd {n : ℕ} (hn : 0 < n)
    (f : HahnSeries ℤ k) {q : ℤ} (hq : ¬ (n : ℤ) ∣ q) :
    (laurentScale hn f).coeff q = 0 := by
  apply embDomain_of_notMem_range
  rintro ⟨z, hz⟩
  exact hq ⟨z, hz.symm⟩

/-- The j-th coefficient series after grouping exponents modulo n. -/
def laurentResiduePart {n : ℕ} (hn : 0 < n) (j : Fin n)
    (f : HahnSeries ℤ k) : HahnSeries ℤ k where
  coeff q := f.coeff ((n : ℤ) * q + j.val)
  isPWO_support' := by
    rw [Set.isPWO_iff_exists_monotone_subseq]
    intro g hg
    obtain ⟨e, he⟩ := f.isPWO_support.exists_monotone_subseq
      (f := fun i => (n : ℤ) * g i + j.val) hg
    refine ⟨e, ?_⟩
    intro a b hab
    have h := he hab
    dsimp only [Function.comp_apply] at h ⊢
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    nlinarith

theorem laurentResiduePart_coeff {n : ℕ} (hn : 0 < n) (j : Fin n)
    (f : HahnSeries ℤ k) (q : ℤ) :
    (laurentResiduePart hn j f).coeff q = f.coeff ((n : ℤ) * q + j.val) := rfl



/-- Every integral exponent has a unique-residue representative in Fin n. -/
theorem laurentExponent_decomposition {n : ℕ} (hn : 0 < n) (z : ℤ) :
    ∃ (j : Fin n) (q : ℤ), (n : ℤ) * q + j.val = z := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let j : Fin n := ⟨(z % (n : ℤ)).toNat, by
    have h := Int.emod_lt_of_pos z hn'
    have h0 := Int.emod_nonneg z hn'.ne'
    omega⟩
  refine ⟨j, z / n, ?_⟩
  dsimp [j]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg z hn'.ne')]
  exact Int.mul_ediv_add_emod z n

/-- Assemble one Laurent coefficient series in each residue class. -/
def laurentGrouped {n : ℕ} (hn : 0 < n) (p : Fin n → HahnSeries ℤ k) :
    HahnSeries ℤ k := ∑ j, single (j.val : ℤ) 1 * laurentScale hn (p j)

theorem laurentGrouped_coeff {n : ℕ} (hn : 0 < n)
    (p : Fin n → HahnSeries ℤ k) (j : Fin n) (q : ℤ) :
    (laurentGrouped hn p).coeff ((n : ℤ) * q + j.val) = (p j).coeff q := by
  classical
  rw [laurentGrouped, coeff_sum]
  rw [Finset.sum_eq_single j]
  · rw [coeff_single_mul, one_mul, add_sub_cancel_right, laurentScale_coeff]
  · intro i _ hij
    rw [coeff_single_mul, one_mul]
    apply laurentScale_coeff_of_not_dvd
    intro hdiv
    have hd : (n : ℤ) ∣ (j.val : ℤ) - i.val := by
      convert dvd_sub hdiv (dvd_mul_right (n : ℤ) q) using 1; ring
    have hmod : (i.val : ℤ) % n = (j.val : ℤ) % n := Int.modEq_iff_dvd.mpr hd
    rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt),
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)] at hmod
    exact hij (Fin.ext (Int.natCast_inj.mp hmod))
  · simp

/-- Actual existence of the finite Laurent expansion over k((tau^n)). -/
theorem laurentGrouped_residueParts {n : ℕ} (hn : 0 < n) (f : HahnSeries ℤ k) :
    laurentGrouped hn (fun j => laurentResiduePart hn j f) = f := by
  ext z
  obtain ⟨j, q, hz⟩ := laurentExponent_decomposition hn z
  rw [← hz, laurentGrouped_coeff, laurentResiduePart_coeff, hz]

/-- Uniqueness of the expansion; this proves independence as well as spanning. -/
theorem laurentGrouped_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (laurentGrouped (k := k) hn) := by
  intro p p' h
  funext j
  ext q
  have hc := congrArg (fun f : HahnSeries ℤ k => f.coeff ((n : ℤ) * q + j.val)) h
  simpa only [laurentGrouped_coeff] using hc

/-- Canonical coordinates of the finite Laurent expansion. -/
def laurentGroupingEquiv {n : ℕ} (hn : 0 < n) :
    (Fin n → HahnSeries ℤ k) ≃ HahnSeries ℤ k where
  toFun := laurentGrouped hn
  invFun f j := laurentResiduePart hn j f
  left_inv p := by
    apply laurentGrouped_injective hn
    exact laurentGrouped_residueParts hn _
  right_inv := laurentGrouped_residueParts hn


/-- The actual copy of k((t)) inside k((tau)), with t = tau^n. -/
abbrev laurentPowerSubfield {n : ℕ} (hn : 0 < n) : Subfield (HahnSeries ℤ k) :=
  (laurentScale (k := k) hn).fieldRange

/-- Identify the copy of the base with the original Laurent-series field. -/
def laurentScaleEquiv {n : ℕ} (hn : 0 < n) :
    HahnSeries ℤ k ≃+* laurentPowerSubfield (k := k) hn :=
  (laurentScale hn).rangeRestrictFieldEquiv

theorem laurentBaseCombination_eq {n : ℕ} (hn : 0 < n)
    (p : Fin n → laurentPowerSubfield (k := k) hn) :
    Fintype.linearCombination (laurentPowerSubfield (k := k) hn)
      (fun j : Fin n => (single (j.val : ℤ) 1 : HahnSeries ℤ k)) p =
      laurentGrouped hn (fun j => (laurentScaleEquiv hn).symm (p j)) := by
  classical
  rw [Fintype.linearCombination_apply, laurentGrouped]
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.smul_def]
  change (p j : HahnSeries ℤ k) * single (j.val : ℤ) 1 =
    single (j.val : ℤ) 1 * laurentScale hn ((laurentScale hn).rangeRestrictFieldEquiv.symm (p j))
  rw [RingHom.rangeRestrictFieldEquiv_apply_symm_apply, mul_comm]

/-- The finite expansion is linear over the actual embedded base field. -/
def laurentPowerCoordinates {n : ℕ} (hn : 0 < n) :
    (Fin n → laurentPowerSubfield (k := k) hn) ≃ₗ[laurentPowerSubfield (k := k) hn]
      HahnSeries ℤ k :=
  LinearEquiv.ofBijective
    (Fintype.linearCombination (laurentPowerSubfield (k := k) hn)
      (fun j : Fin n => (single (j.val : ℤ) 1 : HahnSeries ℤ k))) (by
    constructor
    · intro p p' h
      rw [laurentBaseCombination_eq, laurentBaseCombination_eq] at h
      have h := laurentGrouped_injective hn h
      funext j
      exact (laurentScaleEquiv hn).symm.injective (congrFun h j)
    · intro f
      refine ⟨fun j => laurentScaleEquiv hn (laurentResiduePart hn j f), ?_⟩
      rw [laurentBaseCombination_eq]
      simpa only [RingEquiv.symm_apply_apply] using laurentGrouped_residueParts hn f)

/-- The displayed powers 1,tau,...,tau^(n-1) form a genuine power basis. -/
def laurentPowerBasis {n : ℕ} (hn : 0 < n) :
    PowerBasis (laurentPowerSubfield (k := k) hn) (HahnSeries ℤ k) where
  gen := single 1 1
  dim := n
  basis := (Pi.basisFun (laurentPowerSubfield (k := k) hn) (Fin n)).map
    (laurentPowerCoordinates hn)
  basis_eq_pow j := by
    classical
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    change Fintype.linearCombination (laurentPowerSubfield (k := k) hn)
      (fun j : Fin n => (single (j.val : ℤ) 1 : HahnSeries ℤ k))
      (Pi.single j 1) = single 1 1 ^ j.val
    rw [Fintype.linearCombination_apply_single, one_smul, single_pow]
    simp

theorem laurentPowerBasis_degree {n : ℕ} (hn : 0 < n) :
    Module.finrank (laurentPowerSubfield (k := k) hn) (HahnSeries ℤ k) = n := by
  have := (laurentPowerBasis (k := k) hn).finite
  simpa only [laurentPowerBasis] using (laurentPowerBasis (k := k) hn).finrank

theorem laurentPowerBasis_adjoin {n : ℕ} (hn : 0 < n) :
    Algebra.adjoin (laurentPowerSubfield (k := k) hn)
      ({single 1 1} : Set (HahnSeries ℤ k)) = ⊤ :=
  (laurentPowerBasis hn).adjoin_gen_eq_top


/-- The base uniformizer t as an element of the embedded base field. -/
def laurentBaseUniformizer {n : ℕ} (hn : 0 < n) : laurentPowerSubfield (k := k) hn :=
  laurentScaleEquiv hn (single 1 1)

theorem laurentUniformizer_pow {n : ℕ} (hn : 0 < n) :
    (single 1 1 : HahnSeries ℤ k) ^ n =
      algebraMap (laurentPowerSubfield (k := k) hn) (HahnSeries ℤ k)
        (laurentBaseUniformizer hn) := by
  change (single 1 1 : HahnSeries ℤ k) ^ n = laurentScale hn (single 1 1)
  rw [single_pow]
  change single (n • (1 : ℤ)) ((1 : k) ^ n) =
    embDomain _ (single 1 1 : HahnSeries ℤ k)
  rw [embDomain_single]
  simp [laurentExponentMap]

theorem laurentUniformizer_minpoly {n : ℕ} (hn : 0 < n) :
    minpoly (laurentPowerSubfield (k := k) hn) (single 1 1 : HahnSeries ℤ k) =
      Polynomial.X ^ n - Polynomial.C (laurentBaseUniformizer hn) := by
  let pb := laurentPowerBasis (k := k) hn
  have hi : IsIntegral (laurentPowerSubfield (k := k) hn)
      (single 1 1 : HahnSeries ℤ k) := pb.isIntegral_gen
  have hd : minpoly (laurentPowerSubfield (k := k) hn) (single 1 1 : HahnSeries ℤ k) ∣
      Polynomial.X ^ n - Polynomial.C (laurentBaseUniformizer hn) := by
    apply minpoly.dvd
    simp [laurentUniformizer_pow hn]
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi)
    (Polynomial.monic_X_pow_sub_C _ hn.ne') hd
  rw [Polynomial.natDegree_X_pow_sub_C]
  exact pb.natDegree_minpoly.ge

theorem laurentUniformizer_irreducible {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (laurentBaseUniformizer (k := k) hn)) := by
  rw [← laurentUniformizer_minpoly hn]
  exact minpoly.irreducible (laurentPowerBasis (k := k) hn).isIntegral_gen

end DiamondIntegral.Section5
