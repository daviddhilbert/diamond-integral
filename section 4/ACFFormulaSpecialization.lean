import «section 4».ACFPrimeSpecialization

/-! Finite parameter tuples can be specialized together with any ring-
language formula they satisfy. Definability over a field containing the
specialized parameter values is retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.ACFFormulaSpecialization
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem formula_specializes {K P : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [FirstOrder.Ring.CompatibleRing K] [Finite P]
    (φ : Language.ring.Formula P) (v : P → K) (hφ : φ.Realize v) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ∃ w : P → AlgebraicClosure (ZMod p), φ.Realize w := by
  let ψ : Language.ring.Sentence := (φ.relabel (Sum.inr : P → Empty ⊕ P)).iExs P
  have hψ : K ⊨ ψ := by
    simpa only [ψ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
      Sum.elim_comp_inr] using (show ∃ w : P → K, φ.Realize w from ⟨v, hφ⟩)
  obtain ⟨p, hp, hψ'⟩ := ACFPrimeSpecialization.sentence_specializes ψ hψ
  refine ⟨p, hp, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [ψ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
    Sum.elim_comp_inr] using hψ'

theorem definable_of_parameters {K P α : Type*} [Field K]
    [FirstOrder.Ring.CompatibleRing K] (A : Set K)
    (φ : Language.ring.Formula (P ⊕ α)) (v : P → K) (hv : ∀ i, v i ∈ A) :
    A.Definable Language.ring {x | φ.Realize (Sum.elim v x)} := by
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨φ.relabel (Sum.map (fun i => (⟨v i, hv i⟩ : A)) id), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Formula.realize_relabel]
  have he : Sum.elim (fun a : A => a.val) x ∘ Sum.map (fun i => (⟨v i, hv i⟩ : A)) id =
      Sum.elim v x := by
    funext z
    cases z <;> rfl
  rw [he]

end DiamondIntegral.Section4.ACFFormulaSpecialization
