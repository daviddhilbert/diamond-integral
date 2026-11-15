import Mathlib.ModelTheory.Topology.Types

/-! A semantic first-order cover valid in all models has a finite
subcover. This will be applied to rational graph descriptions and to
complete finite witness packages, rather than to selected model points. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language

theorem finite_formula_cover {L : Language.{0, 0}} {α I : Type} (T : L.Theory)
    (φ : L.Formula α) (ψ : I → L.Formula α)
    (hc : ∀ M : Theory.ModelType.{0, 0, 0} T, ∀ v : α → M, φ.Realize v → ∃ i, (ψ i).Realize v) :
    ∃ s : Finset I, ∀ M : Theory.ModelType.{0, 0, 0} T, ∀ v : α → M,
      φ.Realize v → ∃ i ∈ s, (ψ i).Realize v := by
  let A := T.typesWith (Formula.equivSentence φ)
  let U : I → Set (T.CompleteType α) := fun i => T.typesWith (Formula.equivSentence (ψ i))
  have hcover : A ⊆ ⋃ i, U i := by
    intro p hp
    obtain ⟨M, v, rfl⟩ := Theory.exists_modelType_is_realized_in T p
    have hφ : φ.Realize v := Theory.CompleteType.formula_mem_typeOf.mp hp
    obtain ⟨i, hi⟩ := hc M v hφ
    exact Set.mem_iUnion.mpr ⟨i, Theory.CompleteType.formula_mem_typeOf.mpr hi⟩
  have hA : IsCompact A := (CompleteType.isClosed_typesWith _).isCompact
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover U (fun i => CompleteType.isOpen_typesWith _) hcover
  refine ⟨s, ?_⟩
  intro M v hv
  have hp : T.typeOf v ∈ A := Theory.CompleteType.formula_mem_typeOf.mpr hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hp)
  obtain ⟨his, hψ⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, his, Theory.CompleteType.formula_mem_typeOf.mp hψ⟩

end DiamondIntegral.Section5
