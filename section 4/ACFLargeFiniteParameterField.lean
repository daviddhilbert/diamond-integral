import «section 4».ACFPrimeSpecialization
import Mathlib.Data.Fintype.EquivFin

/-! A finite parameter set in an algebraic closure of a prime field is
contained in finite fields of arbitrarily large cardinality. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.ACFLargeFiniteParameterField

theorem exists_large (p : ℕ) [Fact p.Prime]
    (A : Set (AlgebraicClosure (ZMod p))) (hA : A.Finite) (N : ℕ) :
    ∃ E : IntermediateField (ZMod p) (AlgebraicClosure (ZMod p)),
      Finite E ∧ IsGalois E (AlgebraicClosure (ZMod p)) ∧ A ⊆ E ∧ N < Nat.card E := by
  let f : Fin (N + 1) → AlgebraicClosure (ZMod p) := fun i =>
    Infinite.natEmbedding (AlgebraicClosure (ZMod p)) i.val
  have hf : Function.Injective f := (Infinite.natEmbedding _).injective.comp Fin.val_injective
  obtain ⟨E, hEfin, hEgal, hE⟩ := ACFPrimeSpecialization.finite_parameter_field p
    (A ∪ Set.range f) (hA.union (Set.finite_range f))
  letI : Finite E := hEfin
  let g : Fin (N + 1) → E := fun i => ⟨f i, hE (Or.inr ⟨i, rfl⟩)⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hf (congrArg Subtype.val hij)
  have hc : N + 1 ≤ Nat.card E := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using Nat.card_le_card_of_injective g hg
  exact ⟨E, hEfin, hEgal, fun _ ha => hE (Or.inl ha), Nat.lt_of_succ_le hc⟩

end DiamondIntegral.Section4.ACFLargeFiniteParameterField
