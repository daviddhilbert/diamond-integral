import «section 8».GammaHalfspaces
import «section 8».RationalValues

/-! Lattice points of the value group and integer points of rational traces.

For `π > 1` in the value group `Γ` and `m ≥ 1`, the points of `Γⁿ` all of whose coordinates lie in
the lattice `π^{m⁻¹ℤ}` (`InLattice π m`) are the points `latticePoint π m x`, `x ∈ ℤⁿ`, with
`latticePoint π m x i = π^{x (rev i) / m}` (coordinates reversed, as in `ratTrace`). Hence the
lattice points of `X ⊆ Γⁿ` at level `m` correspond bijectively to the integer points `x` with
`x / m` in the rational trace of `X` (`finsum_lattice`), and an integral affine weight
`∏ γᵢ^{aᵢ} · π^b` has rational value `(∑ aᵢ x_{rev i} + b m) / m` at `latticePoint π m x`
(`ratValue_affine_latticePoint`). -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.GammaCells

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ] [RootableBy Γ ℕ]

theorem eq_qpow_of_ι {π γ : Γ} {q : ℚ} (h : ι γ = q • ι π) : γ = qpow π q :=
  ι_injective (by rw [h, ι_qpow])

theorem qpow_injective {π : Γ} (hπ : 1 < π) : Function.Injective (qpow π) := by
  intro q r h
  have h' := congrArg ι h
  rw [ι_qpow, ι_qpow] at h'
  exact smul_left_injective ℚ (pos_ι_of_one_lt hπ).ne' h'

omit [LinearOrder Γ] [IsOrderedMonoid Γ] in
theorem isRationalValue_qpow (π : Γ) (q : ℚ) : IsRationalValue π (qpow π q) :=
  ⟨q.den, q.den_ne_zero, q.num, qpow_pow_den π q⟩

theorem ratValue_qpow {π : Γ} (hπ : 1 < π) (q : ℚ) : ratValue π (qpow π q) = q := by
  rw [ratValue_eq hπ q.den_ne_zero (qpow_pow_den π q), Rat.num_div_den]

theorem qpow_div_pow (π : Γ) (z : ℤ) {m : ℕ} (hm : m ≠ 0) :
    qpow π ((z : ℚ) / m) ^ m = π ^ z := by
  apply ι_injective
  rw [ι_npow, ι_qpow, ι_zpow_rat, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  field_simp

theorem inLattice_qpow (π : Γ) (z : ℤ) {m : ℕ} (hm : m ≠ 0) :
    InLattice π m (qpow π ((z : ℚ) / m)) :=
  ⟨z, qpow_div_pow π z hm⟩

theorem eq_qpow_of_inLattice {π : Γ} {m : ℕ} (hm : m ≠ 0) {γ : Γ} (h : InLattice π m γ) :
    ∃ z : ℤ, γ = qpow π ((z : ℚ) / m) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z, HasUniqueRoots.pow_left_injective hm (by
    change γ ^ m = qpow π ((z : ℚ) / m) ^ m
    rw [hz, qpow_div_pow π z hm])⟩

/-- The point of `Γⁿ` of an integer vector at level `m`, coordinates reversed. -/
def latticePoint (π : Γ) {n : ℕ} (m : ℕ) (x : Fin n → ℤ) : Fin n → Γ :=
  fun i => qpow π ((x (Fin.rev i) : ℚ) / m)

theorem latticePoint_inLattice (π : Γ) {n m : ℕ} (hm : m ≠ 0) (x : Fin n → ℤ) (i : Fin n) :
    InLattice π m (latticePoint π m x i) :=
  inLattice_qpow π _ hm

theorem latticePoint_injective {π : Γ} (hπ : 1 < π) {n m : ℕ} (hm : m ≠ 0) :
    Function.Injective (latticePoint π (n := n) m) := by
  intro x y h
  funext j
  have h1 := congrFun h (Fin.rev j)
  simp only [latticePoint, Fin.rev_rev] at h1
  have h2 := qpow_injective hπ h1
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [div_left_inj' hmq] at h2
  exact_mod_cast h2

theorem image_latticePoint {π : Γ} {n m : ℕ} (hm : m ≠ 0) (X : Set (Fin n → Γ)) :
    latticePoint π m '' {x | latticePoint π m x ∈ X} = {γ | γ ∈ X ∧ ∀ i, InLattice π m (γ i)} := by
  ext γ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, latticePoint_inLattice π hm x⟩
  · rintro ⟨hγ, hl⟩
    choose z hz using fun i => eq_qpow_of_inLattice hm (hl i)
    refine ⟨fun j => z (Fin.rev j), ?_, ?_⟩
    · have : latticePoint π m (fun j => z (Fin.rev j)) = γ := by
        funext i; simp only [latticePoint, Fin.rev_rev]; exact (hz i).symm
      show latticePoint π m _ ∈ X
      rw [this]; exact hγ
    · funext i; simp only [latticePoint, Fin.rev_rev]; exact (hz i).symm

/-- Sums over the lattice points of `X` at level `m` are sums over integer vectors. -/
theorem finsum_lattice {π : Γ} (hπ : 1 < π) {n m : ℕ} (hm : m ≠ 0) (X : Set (Fin n → Γ))
    {R : Type*} [AddCommMonoid R] (F : (Fin n → Γ) → R) :
    ∑ᶠ x ∈ {x | latticePoint π m x ∈ X}, F (latticePoint π m x) =
      ∑ᶠ γ ∈ {γ | γ ∈ X ∧ ∀ i, InLattice π m (γ i)}, F γ := by
  rw [← image_latticePoint hm X, finsum_mem_image (latticePoint_injective hπ hm).injOn]

/-- The rational value of an integral affine weight at a lattice point. -/
theorem ratValue_affine_latticePoint {π : Γ} (hπ : 1 < π) {n m : ℕ} (hm : m ≠ 0)
    (a : Fin n → ℤ) (b : ℤ) (x : Fin n → ℤ) :
    (m : ℚ) * ratValue π ((∏ i, latticePoint π m x i ^ a i) * π ^ b) =
      ∑ i, a i * x (Fin.rev i) + b * m := by
  set q : ℚ := (∑ i, (a i : ℚ) * x (Fin.rev i)) / m + b
  have hι : ι ((∏ i, latticePoint π m x i ^ a i) * π ^ b) = q • ι π := by
    rw [ι_mul, ι_prod, ι_zpow_rat]
    simp only [ι_zpow_rat, latticePoint, ι_qpow, smul_smul, q, add_smul, Finset.sum_smul,
      div_eq_mul_inv, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  rw [eq_qpow_of_ι hι, ratValue_qpow hπ]
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simp only [q]
  field_simp
  push_cast
  ring

end DiamondIntegral.Section8.GammaCells
