import «section 3».IntegerCharacters
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3

theorem integerBasis_dual_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (v : Fin n → ℤ) (j : Fin n) :
    (∑ i, b.repr (Pi.single i 1) j * v i) = b.repr v j := by
  have he := congrArg (b.coord j) ((Pi.basisFun ℤ (Fin n)).sum_repr v)
  simpa only [map_sum,map_smul,Pi.basisFun_repr,Pi.basisFun_apply,Module.Basis.coord_apply,smul_eq_mul,mul_comm] using he

/-- Fewer integral columns than rows leave a nonzero integral character
annihilating every column. Smith reduction avoids adding rational choices. -/
theorem integerMatrix_left_kernel_of_fewer_columns {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℤ)
    (hmn : m < n) :
    ∃ e : Fin n → ℤ, e ≠ 0 ∧ ∀ j, (∑ i, e i * A i j) = 0 := by
  let N := Submodule.span ℤ (Set.range A.col)
  obtain ⟨r,F⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin n))
  have hr : r ≤ m := by
    have h := finrank_range_le_card (R := ℤ) A.col
    change Module.finrank ℤ N ≤ Fintype.card (Fin m) at h
    simpa only [Module.finrank_eq_card_basis F.bN,Fintype.card_fin] using h
  have hns : ¬ Function.Surjective F.f := by
    intro h
    have hh := Fintype.card_le_of_surjective F.f h
    simp only [Fintype.card_fin] at hh
    omega
  have hj : ∃ j, j ∉ Set.range F.f := by
    by_contra hn
    apply hns
    intro j
    by_contra hj
    exact hn ⟨j,hj⟩
  obtain ⟨j,hj⟩ := hj
  let e : Fin n → ℤ := fun i => F.bM.repr (Pi.single i 1) j
  have he : e ≠ 0 := by
    intro he
    have hd := integerBasis_dual_apply F.bM (F.bM j) j
    change (∑ i, e i * F.bM j i) = F.bM.repr (F.bM j) j at hd
    rw [he] at hd
    simpa using hd
  refine ⟨e,he,?_⟩
  intro k
  have hc : A.col k ∈ N := Submodule.subset_span (Set.mem_range_self k)
  exact (integerBasis_dual_apply F.bM (A.col k) j).trans
    (F.repr_eq_zero_of_notMem_range ⟨A.col k,hc⟩ hj)
end DiamondIntegral.Section3
