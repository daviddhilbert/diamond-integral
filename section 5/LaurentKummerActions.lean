import «section 5».FiniteKummer
import «section 5».LaurentKummerBasis
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The finite Kummer classification specialized to actual Laurent series.
The basis, degree, generation and irreducibility have been proved in
LaurentKummerBasis; none of these is an accepted input here. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

/-- Constant coefficients belong to the actual embedded base. -/
def laurentBaseConstant {n : ℕ} (hn : 0 < n) :
    k →+* laurentPowerSubfield (k := k) hn :=
  (laurentScaleEquiv hn).toRingHom.comp C

theorem laurentBaseConstant_coe {n : ℕ} (hn : 0 < n) (c : k) :
    (laurentBaseConstant hn c : HahnSeries ℤ k) = C c := by
  change laurentScale hn (C c) = C c
  exact embDomainRingHom_C

/-- All finite Kummer automorphisms of k((tau))/k((tau^n)), with
character values in k, provided k contains a primitive n-th root. -/
def laurentKummerEquiv {n : ℕ} (hn : 0 < n) {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    ((HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k)) ≃*
      rootsOfUnity n k := by
  letI : NeZero n := ⟨hn.ne'⟩
  let c := laurentBaseConstant (k := k) hn
  exact (finiteKummerEquiv (hζ.map_of_injective c.injective)
    (laurentUniformizer_irreducible hn) (laurentUniformizer_pow hn)
    (laurentPowerBasis_adjoin hn)).trans
      (rootsOfUnityEquivOfPrimitiveRoots c.injective
        ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩).symm

theorem laurentKummerEquiv_root {n : ℕ} (hn : 0 < n) {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k)) :
    σ (single 1 1) = C ((laurentKummerEquiv hn hζ σ).val : k) * single 1 1 := by
  letI : NeZero n := ⟨hn.ne'⟩
  let c := laurentBaseConstant (k := k) hn
  let e := finiteKummerEquiv (hζ.map_of_injective c.injective)
    (laurentUniformizer_irreducible hn) (laurentUniformizer_pow hn)
    (laurentPowerBasis_adjoin hn)
  let u := rootsOfUnityEquivOfPrimitiveRoots c.injective
    ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩
  have h := finiteKummerEquiv_smul (hζ.map_of_injective c.injective)
    (laurentUniformizer_irreducible hn) (laurentUniformizer_pow hn)
    (laurentPowerBasis_adjoin hn) σ
  change ((e σ).val.val : laurentPowerSubfield (k := k) hn) • single 1 1 = σ (single 1 1) at h
  have hu : c ((u.symm (e σ)).val : k) = ((e σ).val.val : laurentPowerSubfield (k := k) hn) :=
    rootsOfUnityEquivOfPrimitiveRoots_symm_apply c.injective
      ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ (e σ)
  rw [← hu, Algebra.smul_def] at h
  change (laurentBaseConstant hn ((u.symm (e σ)).val : k) : HahnSeries ℤ k) *
    single 1 1 = σ (single 1 1) at h
  rw [laurentBaseConstant_coe] at h
  exact h.symm


/-- The action on the displayed power basis is diagonal. -/
theorem laurentKummerEquiv_single {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k))
    (j : ℕ) :
    σ (single (j : ℤ) 1) =
      C (((laurentKummerEquiv hn hζ σ).val : k) ^ j) * single (j : ℤ) 1 := by
  have h := congrArg (fun x : HahnSeries ℤ k => x ^ j) (laurentKummerEquiv_root hn hζ σ)
  simpa only [mul_pow, ← map_pow, single_pow, one_pow, nsmul_eq_mul, mul_one] using h

/-- The action on an arbitrary Laurent series, in finite expansion coordinates. -/
theorem laurentKummerEquiv_grouped {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k))
    (p : Fin n → HahnSeries ℤ k) :
    σ (laurentGrouped hn p) = laurentGrouped hn
      (fun j => C (((laurentKummerEquiv hn hζ σ).val : k) ^ j.val) * p j) := by
  classical
  simp only [laurentGrouped, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hfix : σ (laurentScale hn (p j)) = laurentScale hn (p j) :=
    σ.commutes (laurentScaleEquiv hn (p j))
  rw [laurentKummerEquiv_single hn hζ σ j.val, hfix]
  change _ = single (j.val : ℤ) 1 *
    ((laurentScale hn (C (((laurentKummerEquiv hn hζ σ).val : k) ^ j.val))) *
      laurentScale hn (p j))
  rw [show laurentScale hn
    (C (((laurentKummerEquiv hn hζ σ).val : k) ^ j.val)) =
      C (((laurentKummerEquiv hn hζ σ).val : k) ^ j.val) from embDomainRingHom_C]
  ring

/-- Exact coefficient action at every exponent, including negative exponents. -/
theorem laurentKummerEquiv_coeff {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k))
    (f : HahnSeries ℤ k) (j : Fin n) (q : ℤ) :
    (σ f).coeff ((n : ℤ) * q + j.val) =
      ((laurentKummerEquiv hn hζ σ).val : k) ^ j.val * f.coeff ((n : ℤ) * q + j.val) := by
  conv_lhs => rw [← laurentGrouped_residueParts hn f, laurentKummerEquiv_grouped hn hζ σ]
  rw [laurentGrouped_coeff]
  rw [show C (((laurentKummerEquiv hn hζ σ).val : k) ^ j.val) =
    single (0 : ℤ) (((laurentKummerEquiv hn hζ σ).val : k) ^ j.val) from rfl]
  rw [coeff_single_mul, sub_zero, laurentResiduePart_coeff]


/-- Nonzero character factors preserve every coefficient's vanishing. -/
theorem laurentKummerEquiv_coeff_zero_iff {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k))
    (f : HahnSeries ℤ k) (z : ℤ) : (σ f).coeff z = 0 ↔ f.coeff z = 0 := by
  obtain ⟨j, q, rfl⟩ := laurentExponent_decomposition hn z
  rw [laurentKummerEquiv_coeff hn hζ σ f j q]
  exact mul_eq_zero.trans (or_iff_right
    (pow_ne_zero j.val (laurentKummerEquiv hn hζ σ).val.ne_zero))

theorem laurentKummerEquiv_support {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k))
    (f : HahnSeries ℤ k) : (σ f).support = f.support := by
  ext z
  exact not_congr (laurentKummerEquiv_coeff_zero_iff hn hζ σ f z)

/-- Thus every finite-level field automorphism preserves the actual valuation. -/
theorem laurentKummerEquiv_orderTop {n : ℕ} (hn : 0 < n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n)
    (σ : (HahnSeries ℤ k) ≃ₐ[laurentPowerSubfield (k := k) hn] (HahnSeries ℤ k))
    (f : HahnSeries ℤ k) : (σ f).orderTop = f.orderTop := by
  apply le_antisymm
  · rw [le_orderTop_iff_forall]
    intro z hz
    exact (laurentKummerEquiv_coeff_zero_iff hn hζ σ f z).mp
      (coeff_eq_zero_of_lt_orderTop hz)
  · rw [le_orderTop_iff_forall]
    intro z hz
    exact (laurentKummerEquiv_coeff_zero_iff hn hζ σ f z).mpr
      (coeff_eq_zero_of_lt_orderTop hz)

/-- In particular all complex finite levels have the full group mu_n. -/
def complexLaurentKummerEquiv {n : ℕ} (hn : 0 < n) :
    ((HahnSeries ℤ ℂ) ≃ₐ[laurentPowerSubfield (k := ℂ) hn] (HahnSeries ℤ ℂ)) ≃*
      rootsOfUnity n ℂ := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact laurentKummerEquiv hn
    (HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ n).choose_spec

end DiamondIntegral.Section5
