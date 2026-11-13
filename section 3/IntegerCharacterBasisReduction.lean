import «section 3».IntegerRectangularKernel
import «section 3».SmithCharacterFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3

/-- Every nonzero integral character is a nonzero multiple of one row
of an integral basis. Smith reduction supplies the unimodular change. -/
theorem integerCharacter_nonzero_basis_multiple {n : ℕ} (e : Fin n → ℤ) (he : e ≠ 0) :
    ∃ b : Module.Basis (Fin n) ℤ (Fin n → ℤ), ∃ j : Fin n,
      ∃ d : ℤ, d ≠ 0 ∧ e = d • b j := by
  let E : Fin 1 → Fin n → ℤ := fun _ => e
  let N := Submodule.span ℤ (Set.range E)
  have hNe : e ∈ N := Submodule.subset_span ⟨(0 : Fin 1),rfl⟩
  let en : N := ⟨e,hNe⟩
  obtain ⟨r,F⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin n))
  have hrle : r ≤ 1 := by
    have h := finrank_range_le_card (R := ℤ) E
    change Module.finrank ℤ N ≤ Fintype.card (Fin 1) at h
    simpa only [Module.finrank_eq_card_basis F.bN,Fintype.card_fin] using h
  have hrne : r ≠ 0 := by
    intro hr
    have hre : F.bN.repr en = 0 := by
      ext i
      have hi := i.isLt
      omega
    have hz : en = 0 := F.bN.repr.injective (by simpa only [map_zero] using hre)
    exact he (congrArg Subtype.val hz)
  have hr : r = 1 := by omega
  subst r
  have he1 : e = (F.bN.repr en 0) • (F.bN 0).val := by
    have hh := congrArg (fun z : N => z.val) (F.bN.sum_repr en)
    simpa only [Fin.sum_univ_one,Submodule.coe_smul_of_tower] using hh.symm
  rw [F.snf 0,smul_smul] at he1
  refine ⟨F.bM,F.f 0,F.bN.repr en 0 * F.a 0,?_,he1⟩
  intro hd
  rw [hd,zero_smul] at he1
  exact he he1

/-- The resulting coordinate equation involves a nonzero integer power,
so it determines a unique coordinate in a group with unique roots. -/
theorem integerCharacter_nonzero_basis_power {n : ℕ} (e : Fin n → ℤ) (he : e ≠ 0) :
    ∃ b : Module.Basis (Fin n) ℤ (Fin n → ℤ), ∃ j : Fin n,
      ∃ d : ℤ, d ≠ 0 ∧ ∀ {G : Type} [CommGroup G] (γ : Fin n → G),
        integerCharacter e γ = (integerMonomialBasisEquiv b γ j) ^ d := by
  obtain ⟨b,j,d,hd,heq⟩ := integerCharacter_nonzero_basis_multiple e he
  refine ⟨b,j,d,hd,?_⟩
  intro G _ γ
  rw [heq,integerCharacter_smul]
  rfl
end DiamondIntegral.Section3
