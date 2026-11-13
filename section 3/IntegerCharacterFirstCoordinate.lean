import «section 3».IntegerCharacterBasisReduction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical
noncomputable section
namespace DiamondIntegral.Section3

/-- A nonzero character can be placed in the first coordinate of an
integral basis, up to a nonzero integer multiple. -/
theorem integerCharacter_nonzero_first_basis_multiple {m : ℕ}
    (e : Fin (1+m) → ℤ) (he : e ≠ 0) :
    ∃ b : Module.Basis (Fin (1+m)) ℤ (Fin (1+m) → ℤ),
      ∃ d : ℤ, d ≠ 0 ∧ e = d • b 0 := by
  obtain ⟨b,j,d,hd,heq⟩ := integerCharacter_nonzero_basis_multiple e he
  let b' := b.reindex (Equiv.swap j (0 : Fin (1+m)))
  have hb : b' 0 = b j := by simp [b',Module.Basis.reindex_apply]
  exact ⟨b',d,hd,hb.symm ▸ heq⟩

theorem integerCharacter_nonzero_first_basis_power {m : ℕ}
    (e : Fin (1+m) → ℤ) (he : e ≠ 0) :
    ∃ b : Module.Basis (Fin (1+m)) ℤ (Fin (1+m) → ℤ),
      ∃ d : ℤ, d ≠ 0 ∧ ∀ {G : Type} [CommGroup G] (γ : Fin (1+m) → G),
        integerCharacter e γ = (integerMonomialBasisEquiv b γ 0) ^ d := by
  obtain ⟨b,d,hd,heq⟩ := integerCharacter_nonzero_first_basis_multiple e he
  refine ⟨b,d,hd,?_⟩
  intro G _ γ
  rw [heq,integerCharacter_smul]
  rfl
end DiamondIntegral.Section3
