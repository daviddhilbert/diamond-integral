import «section 3».IntegerMonomialBasis
import «section 2».ZeroFaces
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Pure integer-matrix algebra for the relative monomial decomposition of
the inflated-family Fubini theorem.

* `inflated_left_kernel_block`: the saturated left kernel of an integer
  matrix `B` gives `Q ∈ GL_m(ℤ)` (in block-indexed form) such that the first
  rows of `Q * B` vanish and the remaining rows have trivial left kernel.
* `inflatedMonomial_surjective_of_left_kernel`: such a full-row-rank integer
  monomial map is surjective on any divisible subgroup.
* `inflated_rows_extend_of_right_inverse`: right-invertible (primitive) rows
  extend to an integer matrix with a two-sided integer inverse.
* `inflated_relative_block_chart`: the abstract relative chart. For a set
  `S` of `(z,u)` which is a monomial product chart and is invariant under the
  kernel of the value map in its `z` coordinates, a coordinate change acting
  on `u` alone separates one fixed residue block from free coordinates.

Everything is stated with explicit two-sided integer inverses; no input
beyond Mathlib's Smith normal form and PID bases is used. -/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace DiamondIntegral.Section5
open DiamondIntegral.Section3

section Monomial
variable {ι κ G H : Type} [Fintype κ] [CommGroup G] [CommGroup H]

theorem inflatedMonomial_mul (A : Matrix ι κ ℤ) (x y : κ → G) :
    integerMonomialMap A (x * y) = integerMonomialMap A x * integerMonomialMap A y := by
  funext i
  simp only [integerMonomialMap, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem inflatedMonomial_inv (A : Matrix ι κ ℤ) (x : κ → G) :
    integerMonomialMap A x⁻¹ = (integerMonomialMap A x)⁻¹ := by
  funext i
  simp only [integerMonomialMap, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem inflatedMonomial_one_input (A : Matrix ι κ ℤ) :
    integerMonomialMap A (1 : κ → G) = 1 := by
  funext i
  simp only [integerMonomialMap, Pi.one_apply, one_zpow, Finset.prod_const_one]

theorem inflatedMonomial_zero_matrix (x : κ → G) :
    integerMonomialMap (0 : Matrix ι κ ℤ) x = 1 := by
  funext i
  simp only [integerMonomialMap, Matrix.zero_apply, zpow_zero, Finset.prod_const_one,
    Pi.one_apply]

theorem inflatedMonomial_map (φ : G →* H) (A : Matrix ι κ ℤ) (x : κ → G) :
    (fun i => φ (integerMonomialMap A x i)) = integerMonomialMap A (fun j => φ (x j)) := by
  funext i
  simp only [integerMonomialMap, map_prod, map_zpow]

theorem inflatedMonomial_mem (P : Subgroup G) (A : Matrix ι κ ℤ) (x : κ → G)
    (hx : ∀ j, x j ∈ P) (i : ι) : integerMonomialMap A x i ∈ P :=
  Subgroup.prod_mem P (fun j _ => Subgroup.zpow_mem P (hx j) _)

theorem inflatedMonomial_rows {ι' : Type} [Fintype ι'] (A : Matrix ι κ ℤ) (e : ι' → ι)
    (x : κ → G) : integerMonomialMap (A.submatrix e id) x = fun i => integerMonomialMap A x (e i) :=
  rfl

theorem inflatedMonomial_append {n r : ℕ} (A : Matrix ι (Fin (n + r)) ℤ) (z : Fin n → G)
    (u : Fin r → G) :
    integerMonomialMap A (Fin.append z u) =
      integerMonomialMap (A.submatrix id (Fin.castAdd r)) z *
        integerMonomialMap (A.submatrix id (Fin.natAdd n)) u := by
  funext i
  simp only [integerMonomialMap, Pi.mul_apply, Fin.prod_univ_add, Fin.append_left,
    Fin.append_right, Matrix.submatrix_apply, id]

theorem inflatedMonomial_smul_one [Fintype ι] [DecidableEq ι] (d : ℤ) (x : ι → G) :
    integerMonomialMap (d • (1 : Matrix ι ι ℤ)) x = fun i => x i ^ d := by
  funext i
  simp only [integerMonomialMap, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem inflatedMonomial_left_inverse [Fintype ι] [DecidableEq κ] (A : Matrix ι κ ℤ) (A' : Matrix κ ι ℤ)
    (h : A' * A = 1) (x : κ → G) : integerMonomialMap A' (integerMonomialMap A x) = x := by
  rw [integerMonomialMap_comp, h, integerMonomialMap_one]

theorem inflatedMonomial_injective [Fintype ι] [DecidableEq κ] (A : Matrix ι κ ℤ) (A' : Matrix κ ι ℤ)
    (h : A' * A = 1) : Function.Injective (integerMonomialMap (G := G) A) := by
  intro x y hxy
  rw [← inflatedMonomial_left_inverse A A' h x, hxy, inflatedMonomial_left_inverse A A' h y]

/-- Block-diagonal integer matrix in `Fin.append` coordinates. -/
def inflatedBlockDiag {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ)
    (C : Matrix (Fin c) (Fin d) ℤ) : Matrix (Fin (a + c)) (Fin (b + d)) ℤ :=
  Matrix.of fun i j =>
    Fin.append (fun i' => Fin.append (A i') (0 : Fin d → ℤ))
      (fun i' => Fin.append (0 : Fin b → ℤ) (C i')) i j

theorem inflatedBlockDiag_monomial {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ)
    (C : Matrix (Fin c) (Fin d) ℤ) (z : Fin b → G) (u : Fin d → G) :
    integerMonomialMap (inflatedBlockDiag A C) (Fin.append z u) =
      Fin.append (integerMonomialMap A z) (integerMonomialMap C u) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [integerMonomialMap, inflatedBlockDiag, Matrix.of_apply, Fin.prod_univ_add,
      Fin.append_left, Fin.append_right, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one]
  · simp only [integerMonomialMap, inflatedBlockDiag, Matrix.of_apply, Fin.prod_univ_add,
      Fin.append_left, Fin.append_right, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]

theorem inflated_append_eq_iff {α : Type} {a b : ℕ} (x x' : Fin a → α) (y y' : Fin b → α) :
    Fin.append x y = Fin.append x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa only [Fin.append_left] using congrFun h (Fin.castAdd b i)
    · simpa only [Fin.append_right] using congrFun h (Fin.natAdd a i)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem inflated_append_split {α : Type} {a b : ℕ} (x : Fin (a + b) → α) :
    Fin.append (fun i => x (Fin.castAdd b i)) (fun i => x (Fin.natAdd a i)) = x :=
  Fin.append_castAdd_natAdd

end Monomial

section IntegerAlgebra

/-- A zero left block of a right-invertible matrix forces its right block to
be right invertible. -/
theorem inflated_right_block_right_inverse {h n r : ℕ} (T : Matrix (Fin h) (Fin (n + r)) ℤ)
    (S : Matrix (Fin (n + r)) (Fin h) ℤ) (hTS : T * S = 1)
    (hzero : ∀ i j, T i (Fin.castAdd r j) = 0) :
    T.submatrix id (Fin.natAdd n) * S.submatrix (Fin.natAdd n) id = 1 := by
  rw [← hTS]
  ext i k
  simp only [Matrix.mul_apply, Fin.sum_univ_add, hzero, zero_mul, Finset.sum_const_zero,
    zero_add, Matrix.submatrix_apply, id]

/-- Primitive rows extend to an integral basis: an integer matrix with an
integer right inverse is the top block of a matrix with a two-sided integer
inverse. -/
theorem inflated_rows_extend_of_right_inverse {h r : ℕ} (A : Matrix (Fin h) (Fin r) ℤ)
    (Y : Matrix (Fin r) (Fin h) ℤ) (hAY : A * Y = 1) :
    ∃ ℓ : ℕ, ∃ N : Matrix (Fin (h + ℓ)) (Fin r) ℤ, ∃ Ninv : Matrix (Fin r) (Fin (h + ℓ)) ℤ,
      N * Ninv = 1 ∧ Ninv * N = 1 ∧ h + ℓ = r ∧ ∀ i j, N (Fin.castAdd ℓ i) j = A i j := by
  classical
  let α : (Fin r → ℤ) →ₗ[ℤ] (Fin h → ℤ) := Matrix.mulVecLin A
  let σ : (Fin h → ℤ) →ₗ[ℤ] (Fin r → ℤ) := Matrix.mulVecLin Y
  have hασ : ∀ a, α (σ a) = a := by
    intro a
    change A *ᵥ (Y *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
  let K : Submodule ℤ (Fin r → ℤ) := LinearMap.ker α
  obtain ⟨ℓ, bK⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin r)) K
  let ρ : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) := LinearMap.id - σ ∘ₗ α
  have hπ : ∀ v, ρ v ∈ K := by
    intro v
    change α (v - σ (α v)) = 0
    rw [map_sub, hασ, sub_self]
  let π : (Fin r → ℤ) →ₗ[ℤ] K := ρ.codRestrict K hπ
  let κ : K ≃ₗ[ℤ] (Fin ℓ → ℤ) := bK.equivFun
  let Φ : (Fin r → ℤ) →ₗ[ℤ] (Fin (h + ℓ) → ℤ) :=
    { toFun := fun v => Fin.append (α v) (κ (π v))
      map_add' := fun v w => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left, map_add, Pi.add_apply]
        · simp only [Fin.append_right, map_add, Pi.add_apply]
      map_smul' := fun c v => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left, map_smul, Pi.smul_apply, RingHom.id_apply]
        · simp only [Fin.append_right, map_smul, Pi.smul_apply, RingHom.id_apply] }
  let Ψ : (Fin (h + ℓ) → ℤ) →ₗ[ℤ] (Fin r → ℤ) :=
    σ ∘ₗ LinearMap.funLeft ℤ ℤ (Fin.castAdd ℓ) +
      K.subtype ∘ₗ (κ.symm : (Fin ℓ → ℤ) →ₗ[ℤ] K) ∘ₗ LinearMap.funLeft ℤ ℤ (Fin.natAdd h)
  have hΦ : ∀ v, Φ v = Fin.append (α v) (κ (π v)) := fun v => rfl
  have hΨ : ∀ w, Ψ w = σ (fun i => w (Fin.castAdd ℓ i)) +
      (κ.symm (fun i => w (Fin.natAdd h i)) : Fin r → ℤ) := fun w => rfl
  have hΨΦ : ∀ v, Ψ (Φ v) = v := by
    intro v
    rw [hΨ, hΦ]
    have h1 : (fun i => Fin.append (α v) (κ (π v)) (Fin.castAdd ℓ i)) = α v :=
      funext fun i => Fin.append_left _ _ i
    have h2 : (fun i => Fin.append (α v) (κ (π v)) (Fin.natAdd h i)) = κ (π v) :=
      funext fun i => Fin.append_right _ _ i
    rw [h1, h2, LinearEquiv.symm_apply_apply]
    change σ (α v) + (v - σ (α v)) = v
    abel
  have hΦΨ : ∀ w, Φ (Ψ w) = w := by
    intro w
    let a : Fin h → ℤ := fun i => w (Fin.castAdd ℓ i)
    let b : Fin ℓ → ℤ := fun i => w (Fin.natAdd h i)
    have hk : α (κ.symm b : Fin r → ℤ) = 0 := (κ.symm b).property
    have hαΨ : α (Ψ w) = a := by
      rw [hΨ, map_add, hασ, hk, add_zero]
    have hπΨ : π (Ψ w) = κ.symm b := by
      apply Subtype.ext
      change Ψ w - σ (α (Ψ w)) = (κ.symm b : Fin r → ℤ)
      rw [hαΨ, hΨ]
      abel
    rw [hΦ, hαΨ, hπΨ, LinearEquiv.apply_symm_apply]
    exact Fin.append_castAdd_natAdd
  let N := LinearMap.toMatrix' Φ
  let Ninv := LinearMap.toMatrix' Ψ
  have hcompΦΨ : Φ ∘ₗ Ψ = LinearMap.id := LinearMap.ext hΦΨ
  have hcompΨΦ : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext hΨΦ
  have hNN : N * Ninv = 1 := by
    rw [← LinearMap.toMatrix'_comp, hcompΦΨ, LinearMap.toMatrix'_id]
  have hNN' : Ninv * N = 1 := by
    rw [← LinearMap.toMatrix'_comp, hcompΨΦ, LinearMap.toMatrix'_id]
  have hdim : h + ℓ = r := by
    let e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin (h + ℓ) → ℤ) := LinearEquiv.ofLinearMap Φ Ψ hcompΦΨ hcompΨΦ
    have := e.finrank_eq
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    exact this.symm
  refine ⟨ℓ, N, Ninv, hNN, hNN', hdim, ?_⟩
  intro i j
  change Φ (Pi.single j 1) (Fin.castAdd ℓ i) = A i j
  rw [hΦ, Fin.append_left]
  change (A *ᵥ Pi.single j 1) i = A i j
  rw [Matrix.mulVec_single_one]
  rfl

/-- The saturated left kernel of an integer matrix. The first `h` rows of
`Q` form a basis of the left kernel of `B`; the remaining rows of `Q * B`
have trivial integer left kernel. -/
theorem inflated_left_kernel_block {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) :
    ∃ h p : ℕ, ∃ Q : Matrix (Fin (h + p)) (Fin m) ℤ, ∃ Qinv : Matrix (Fin m) (Fin (h + p)) ℤ,
      Q * Qinv = 1 ∧ Qinv * Q = 1 ∧
      (∀ i j, (Q * B) (Fin.castAdd p i) j = 0) ∧
      ∀ c : Fin p → ℤ, c ᵥ* (Q * B).submatrix (Fin.natAdd h) id = 0 → c = 0 := by
  classical
  let L : Submodule ℤ (Fin m → ℤ) := LinearMap.ker (Matrix.vecMulLinear B)
  have hL : ∀ x, x ∈ L ↔ x ᵥ* B = 0 := fun x => Iff.rfl
  obtain ⟨k, F⟩ := L.smithNormalForm (Pi.basisFun ℤ (Fin m))
  have hsat : ∀ i, F.bM (F.f i) ∈ L := by
    intro i
    have hN : F.a i • F.bM (F.f i) ∈ L := by
      rw [← F.snf i]
      exact (F.bN i).property
    have ha : F.a i ≠ 0 := by
      intro h0
      apply F.bN.ne_zero i
      apply Subtype.ext
      rw [F.snf i, h0, zero_smul]
      rfl
    rw [hL] at hN ⊢
    rw [Matrix.smul_vecMul] at hN
    exact (smul_eq_zero.mp hN).resolve_left ha
  let C := Section2.zeroFaceChart (Set.range F.f)
  let e := C.coordinates
  let Q0 := integerBasisMatrix F.bM
  let Q0inv := integerBasisInverseMatrix F.bM
  have hrow : ∀ (i : Fin (C.zeroArity + C.freeArity)) j,
      (Q0.submatrix e id * B) i j = (F.bM (e i) ᵥ* B) j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.vecMul, dotProduct, Q0,
      integerBasisMatrix]
  refine ⟨C.zeroArity, C.freeArity, Q0.submatrix e id, Q0inv.submatrix id e, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, integerBasis_mul_inverse]
    exact Matrix.submatrix_one_equiv e
  · rw [Matrix.submatrix_mul_equiv, integerBasisInverse_mul, Matrix.submatrix_id_id]
  · intro i j
    rw [hrow]
    have hz : e (Fin.castAdd C.freeArity i) ∈ Set.range F.f := C.zero_mem i
    obtain ⟨i', hi'⟩ := hz
    have h0 := (hL _).mp (hsat i')
    rw [hi'] at h0
    rw [h0]
    rfl
  · intro c hc
    let x : Fin m → ℤ := ∑ i, c i • F.bM (C.freeIndex i)
    have hxB : x ᵥ* B = c ᵥ* (Q0.submatrix e id * B).submatrix (Fin.natAdd C.zeroArity) id := by
      funext j
      simp only [x, Matrix.vecMul, dotProduct, Matrix.submatrix_apply, id, hrow,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Section2.ZeroFaceChart.freeIndex, Finset.mul_sum, e]
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hx : x ∈ L := (hL x).mpr (hxB.trans hc)
    funext i
    have hrepr0 := F.repr_eq_zero_of_notMem_range ⟨x, hx⟩ (C.free_not_mem i)
    change F.bM.repr x (C.freeIndex i) = 0 at hrepr0
    have hinj : Function.Injective C.freeIndex := by
      intro a b hab
      have := C.coordinates.injective hab
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val this))
    have hrepr : F.bM.repr x (C.freeIndex i) = c i := by
      simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp only [Finsupp.single_apply]
        split_ifs with hh
        · exact absurd (hinj hh) hb
        · rfl
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [← hrepr, hrepr0]
    rfl

/-- A full-row-rank integer monomial map is surjective on every divisible
subgroup of a commutative group. -/
theorem inflatedMonomial_surjective_of_left_kernel {G : Type} [CommGroup G] (P : Subgroup G)
    (hdiv : ∀ d : ℤ, d ≠ 0 → ∀ g ∈ P, ∃ x ∈ P, x ^ d = g)
    {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℤ) (hA : ∀ c : Fin p → ℤ, c ᵥ* A = 0 → c = 0)
    (g : Fin p → G) (hg : ∀ i, g i ∈ P) :
    ∃ x : Fin n → G, (∀ j, x j ∈ P) ∧ integerMonomialMap A x = g := by
  classical
  let Gm : Matrix (Fin p) (Fin p) ℤ := A * A.transpose
  have hdet : Gm.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : (c ᵥ* A) ⬝ᵥ (c ᵥ* A) = 0 := by
      calc (c ᵥ* A) ⬝ᵥ (c ᵥ* A) = c ⬝ᵥ (A *ᵥ (c ᵥ* A)) := (Matrix.dotProduct_mulVec c A _).symm
        _ = c ⬝ᵥ (Gm *ᵥ c) := by rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
        _ = 0 := by rw [hc, dotProduct_zero]
    exact hc0 (hA c (dotProduct_self_eq_zero.mp h1))
  let Y : Matrix (Fin n) (Fin p) ℤ := A.transpose * Gm.adjugate
  have hAY : A * Y = Gm.det • (1 : Matrix (Fin p) (Fin p) ℤ) := by
    rw [← Matrix.mul_assoc]
    exact Matrix.mul_adjugate Gm
  choose x hxP hx using fun i => hdiv Gm.det hdet (g i) (hg i)
  refine ⟨integerMonomialMap Y x, inflatedMonomial_mem P Y x hxP, ?_⟩
  rw [integerMonomialMap_comp, hAY, inflatedMonomial_smul_one]
  exact funext hx

end IntegerAlgebra

section RelativeChart
variable {G Γ : Type} [CommGroup G] [CommGroup Γ]

/-- The first `a` coordinates of a block monomial map. -/
def inflatedTop {a b N : ℕ} (M : Matrix (Fin (a + b)) (Fin N) ℤ) (x : Fin N → G) : Fin a → G :=
  integerMonomialMap (M.submatrix (Fin.castAdd b) id) x

/-- The last `b` coordinates of a block monomial map. -/
def inflatedBottom {a b N : ℕ} (M : Matrix (Fin (a + b)) (Fin N) ℤ) (x : Fin N → G) :
    Fin b → G :=
  integerMonomialMap (M.submatrix (Fin.natAdd a) id) x

theorem inflatedTop_apply {a b N : ℕ} (M : Matrix (Fin (a + b)) (Fin N) ℤ) (x : Fin N → G)
    (i : Fin a) : inflatedTop M x i = integerMonomialMap M x (Fin.castAdd b i) := rfl

theorem inflatedBottom_apply {a b N : ℕ} (M : Matrix (Fin (a + b)) (Fin N) ℤ) (x : Fin N → G)
    (i : Fin b) : inflatedBottom M x i = integerMonomialMap M x (Fin.natAdd a i) := rfl

theorem inflatedTop_append_bottom {a b N : ℕ} (M : Matrix (Fin (a + b)) (Fin N) ℤ)
    (x : Fin N → G) : Fin.append (inflatedTop M x) (inflatedBottom M x) = integerMonomialMap M x := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left, inflatedTop_apply]
  · rw [Fin.append_right, inflatedBottom_apply]

/-- The abstract relative monomial chart. Let `v : G →* Γ` be surjective with
divisible kernel. Let `S` be a set of tuples `(z,u)` given, after an integer
change of coordinates `M` with integer inverse, by a residue block `V` of one
value `β` and a full value preimage of `I`. If `S` depends on `z` only through
its values, then an integer coordinate change `N` acting on `u` alone splits
`S` as follows: the first coordinates of `N u` lie in the fixed residue set
`Qt '' V`, and the remaining membership condition depends only on values. -/
theorem inflated_relative_block_chart (v : G →* Γ) (hsurj : Function.Surjective v)
    (hdiv : ∀ d : ℤ, d ≠ 0 → ∀ g ∈ v.ker, ∃ x ∈ v.ker, x ^ d = g)
    {n r m f : ℕ} (M : Matrix (Fin (m + f)) (Fin (n + r)) ℤ)
    (Minv : Matrix (Fin (n + r)) (Fin (m + f)) ℤ) (hM : M * Minv = 1)
    (V : Set (Fin m → G)) (β : Fin m → Γ) (hV : ∀ t ∈ V, (fun i => v (t i)) = β)
    (I : Set (Fin f → Γ)) (hI : I.Nonempty) (S : Set (Fin (n + r) → G))
    (hS : ∀ x, x ∈ S ↔ inflatedTop M x ∈ V ∧ (fun i => v (inflatedBottom M x i)) ∈ I)
    (hinv : ∀ (z z' : Fin n → G) (u : Fin r → G), (fun i => v (z i)) = (fun i => v (z' i)) →
      Fin.append z u ∈ S → Fin.append z' u ∈ S) :
    ∃ h ℓ : ℕ, ∃ N : Matrix (Fin (h + ℓ)) (Fin r) ℤ, ∃ Ninv : Matrix (Fin r) (Fin (h + ℓ)) ℤ,
      ∃ Qt : Matrix (Fin h) (Fin m) ℤ,
      N * Ninv = 1 ∧ Ninv * N = 1 ∧ h + ℓ = r ∧
      (∀ z u, Fin.append z u ∈ S → inflatedTop N u ∈ integerMonomialMap Qt '' V) ∧
      (∀ z u z' u', Fin.append z' u' ∈ S → inflatedTop N u ∈ integerMonomialMap Qt '' V →
        (fun i => v (z i)) = (fun i => v (z' i)) →
        (fun i => v (inflatedBottom N u i)) = (fun i => v (inflatedBottom N u' i)) →
        Fin.append z u ∈ S) := by
  classical
  let Mres : Matrix (Fin m) (Fin (n + r)) ℤ := M.submatrix (Fin.castAdd f) id
  let Bm : Matrix (Fin m) (Fin n) ℤ := Mres.submatrix id (Fin.castAdd r)
  let Am : Matrix (Fin m) (Fin r) ℤ := Mres.submatrix id (Fin.natAdd n)
  have hres : ∀ (z : Fin n → G) (u : Fin r → G), inflatedTop M (Fin.append z u) =
      integerMonomialMap Bm z * integerMonomialMap Am u :=
    fun z u => inflatedMonomial_append Mres z u
  obtain ⟨h, p, Q, Qinv, hQ, hQ', htop, hbot⟩ := inflated_left_kernel_block Bm
  let Qt : Matrix (Fin h) (Fin m) ℤ := Q.submatrix (Fin.castAdd p) id
  let Qb : Matrix (Fin p) (Fin m) ℤ := Q.submatrix (Fin.natAdd h) id
  have hQtB : Qt * Bm = 0 := by
    ext i j
    exact htop i j
  let T : Matrix (Fin h) (Fin (n + r)) ℤ := Qt * Mres
  let S0 : Matrix (Fin (n + r)) (Fin h) ℤ :=
    Minv.submatrix id (Fin.castAdd f) * Qinv.submatrix id (Fin.castAdd p)
  have h1 : Mres * Minv.submatrix id (Fin.castAdd f) = 1 := by
    change M.submatrix (Fin.castAdd f) id * Minv.submatrix id (Fin.castAdd f) = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hM]
    exact Matrix.submatrix_one_embedding ⟨Fin.castAdd f, Fin.castAdd_injective _ _⟩
  have h2 : Qt * Qinv.submatrix id (Fin.castAdd p) = 1 := by
    change Q.submatrix (Fin.castAdd p) id * Qinv.submatrix id (Fin.castAdd p) = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hQ]
    exact Matrix.submatrix_one_embedding ⟨Fin.castAdd p, Fin.castAdd_injective _ _⟩
  have hTS : T * S0 = 1 := by
    calc T * S0 = Qt * (Mres * Minv.submatrix id (Fin.castAdd f)) *
          Qinv.submatrix id (Fin.castAdd p) := by simp only [T, S0, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, h2]
  have hTzero : ∀ i j, T i (Fin.castAdd r j) = 0 := fun i j => congrFun (congrFun hQtB i) j
  have hA'Y := inflated_right_block_right_inverse T S0 hTS hTzero
  obtain ⟨ℓ, N, Ninv, hN, hN', hdim, hNtop⟩ := inflated_rows_extend_of_right_inverse _ _ hA'Y
  have hNQ : N.submatrix (Fin.castAdd ℓ) id = Qt * Am := by
    ext i j
    rw [Matrix.submatrix_apply, hNtop]
    rfl
  have hfix : ∀ u : Fin r → G,
      inflatedTop N u = integerMonomialMap Qt (integerMonomialMap Am u) := by
    intro u
    rw [integerMonomialMap_comp, ← hNQ]
    rfl
  have hQres : ∀ (z : Fin n → G) (u : Fin r → G),
      integerMonomialMap Qt (inflatedTop M (Fin.append z u)) = inflatedTop N u := by
    intro z u
    rw [hres, inflatedMonomial_mul, integerMonomialMap_comp Qt Bm, hQtB,
      inflatedMonomial_zero_matrix, one_mul, hfix]
  have hfwd : ∀ z u, Fin.append z u ∈ S → inflatedTop N u ∈ integerMonomialMap Qt '' V :=
    fun z u hx => ⟨inflatedTop M (Fin.append z u), ((hS _).mp hx).1, hQres z u⟩
  have hVinv : ∀ t ∈ V, ∀ s : Fin n → G, (∀ j, s j ∈ v.ker) →
      t * integerMonomialMap Bm s ∈ V := by
    intro t ht s hs
    obtain ⟨η, hη⟩ := hI
    choose y hy using fun i => hsurj (η i)
    let q : Fin (m + f) → G := Fin.append t y
    let x0 := integerMonomialMap Minv q
    have hMx0 : integerMonomialMap M x0 = q := by
      rw [integerMonomialMap_comp, hM, integerMonomialMap_one]
    have htop0 : inflatedTop M x0 = t := by
      funext i
      rw [inflatedTop_apply, hMx0]
      exact Fin.append_left _ _ i
    have hbot0 : inflatedBottom M x0 = y := by
      funext i
      rw [inflatedBottom_apply, hMx0]
      exact Fin.append_right _ _ i
    have hx0 : x0 ∈ S := by
      rw [hS, htop0, hbot0]
      refine ⟨ht, ?_⟩
      have hyη : (fun i => v (y i)) = η := funext hy
      rw [hyη]
      exact hη
    let z0 : Fin n → G := fun i => x0 (Fin.castAdd r i)
    let u0 : Fin r → G := fun i => x0 (Fin.natAdd n i)
    have hx0' : Fin.append z0 u0 = x0 := inflated_append_split x0
    have hval : (fun i => v (z0 i)) = (fun i => v ((z0 * s) i)) := by
      funext i
      rw [Pi.mul_apply, map_mul, (MonoidHom.mem_ker.mp (hs i)), mul_one]
    have hx1 := hinv z0 (z0 * s) u0 hval (by rw [hx0']; exact hx0)
    have hmem := ((hS _).mp hx1).1
    have hcomp : inflatedTop M (Fin.append (z0 * s) u0) = t * integerMonomialMap Bm s := by
      rw [hres, inflatedMonomial_mul, mul_right_comm, ← hres, hx0', htop0]
    rwa [hcomp] at hmem
  have hkey : ∀ t0 ∈ V, ∀ t : Fin m → G, (fun i => v (t i)) = β →
      integerMonomialMap Qt t = integerMonomialMap Qt t0 → t ∈ V := by
    intro t0 ht0 t hvt hQt
    let k : Fin m → G := t0⁻¹ * t
    have hk : ∀ i, k i ∈ v.ker := by
      intro i
      rw [MonoidHom.mem_ker]
      have e1 : v (t0 i) = β i := congrFun (hV t0 ht0) i
      have e2 : v (t i) = β i := congrFun hvt i
      simp only [k, Pi.mul_apply, Pi.inv_apply, map_mul, map_inv, e1, e2, inv_mul_cancel]
    have hQk : integerMonomialMap Qt k = 1 := by
      simp only [k]
      rw [inflatedMonomial_mul, inflatedMonomial_inv, hQt, inv_mul_cancel]
    have hQbk : ∀ i, integerMonomialMap Qb k i ∈ v.ker := inflatedMonomial_mem v.ker Qb k hk
    obtain ⟨s, hs, hBs⟩ := inflatedMonomial_surjective_of_left_kernel v.ker hdiv
      ((Q * Bm).submatrix (Fin.natAdd h) id) hbot (integerMonomialMap Qb k) hQbk
    have hQeq : integerMonomialMap Q (integerMonomialMap Bm s) = integerMonomialMap Q k := by
      rw [integerMonomialMap_comp]
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have h0 : integerMonomialMap (Q * Bm) s (Fin.castAdd p i) = 1 := by
          simp only [integerMonomialMap, htop, zpow_zero, Finset.prod_const_one]
        rw [h0]
        exact (congrFun hQk i).symm
      · exact congrFun hBs i
    have hBk : integerMonomialMap Bm s = k := inflatedMonomial_injective Q Qinv hQ' hQeq
    have hmem := hVinv t0 ht0 s hs
    rw [hBk] at hmem
    simpa only [k, mul_inv_cancel_left] using hmem
  refine ⟨h, ℓ, N, Ninv, Qt, hN, hN', hdim, hfwd, ?_⟩
  intro z u z' u' hx' hW hz hy
  obtain ⟨t0, ht0, hNt0⟩ := hW
  have hx'S := (hS _).mp hx'
  have htopval : ∀ w : Fin (n + r) → G, inflatedTop M w ∈ V →
      (fun i => v (integerMonomialMap Qt (inflatedTop M w) i)) = integerMonomialMap Qt β := by
    intro w hw
    rw [inflatedMonomial_map v Qt, hV _ hw]
  have hvN : (fun i => v (integerMonomialMap N u i)) = (fun i => v (integerMonomialMap N u' i)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have e1 : v (integerMonomialMap N u (Fin.castAdd ℓ i)) = integerMonomialMap Qt β i := by
        rw [← inflatedTop_apply, ← hNt0, ← hV t0 ht0, ← inflatedMonomial_map v Qt]
      have e2 : v (integerMonomialMap N u' (Fin.castAdd ℓ i)) = integerMonomialMap Qt β i := by
        rw [← inflatedTop_apply, ← hQres z' u']
        exact congrFun (htopval _ hx'S.1) i
      rw [e1, e2]
    · exact congrFun hy i
  have hvu : (fun i => v (u i)) = (fun i => v (u' i)) := by
    have k1 := inflatedMonomial_map v Ninv (integerMonomialMap N u)
    have k2 := inflatedMonomial_map v Ninv (integerMonomialMap N u')
    rw [inflatedMonomial_left_inverse N Ninv hN'] at k1 k2
    rw [k1, k2, hvN]
  have hvx : (fun i => v (Fin.append z u i)) = (fun i => v (Fin.append z' u' i)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact congrFun hz i
    · simp only [Fin.append_right]
      exact congrFun hvu i
  rw [hS]
  constructor
  · apply hkey t0 ht0
    · have k1 := inflatedMonomial_map v (M.submatrix (Fin.castAdd f) id) (Fin.append z u)
      have k2 := inflatedMonomial_map v (M.submatrix (Fin.castAdd f) id) (Fin.append z' u')
      change (fun i => v (inflatedTop M (Fin.append z u) i)) = _ at k1
      change (fun i => v (inflatedTop M (Fin.append z' u') i)) = _ at k2
      rw [k1, hvx, ← k2]
      exact hV _ hx'S.1
    · rw [hQres, hNt0]
  · have k1 := inflatedMonomial_map v (M.submatrix (Fin.natAdd m) id) (Fin.append z u)
    have k2 := inflatedMonomial_map v (M.submatrix (Fin.natAdd m) id) (Fin.append z' u')
    change (fun i => v (inflatedBottom M (Fin.append z u) i)) = _ at k1
    change (fun i => v (inflatedBottom M (Fin.append z' u') i)) = _ at k2
    rw [k1, hvx, ← k2]
    exact hx'S.2

end RelativeChart

end DiamondIntegral.Section5
