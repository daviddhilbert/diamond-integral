import «section 3».FullGammaAdjoinAbstraction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def adjoinGammaTuple (B : Base (M := M)) {n : ℕ} (γ : Fin n → Values.Gamma (M := M)) : Base (M := M) :=
  ⟨B.real,B.gamma ∪ Set.range γ⟩

theorem adjoinGammaTuple_zero (B : Base (M := M)) (γ : Fin 0 → Values.Gamma (M := M)) : adjoinGammaTuple B γ = B := by
  have hr : Set.range γ = ∅ := by
    ext x
    exact ⟨fun ⟨i,_⟩ => i.elim0,False.elim⟩
  cases B
  simp only [adjoinGammaTuple,hr,Set.union_empty]

theorem adjoinGammaTuple_succ (B : Base (M := M)) {n : ℕ} (γ : Fin (n+1) → Values.Gamma (M := M)) :
    adjoinGammaTuple B γ = Section2.adjoinGamma (adjoinGammaTuple B (Fin.init γ)) (γ (Fin.last n)) := by
  have hr : Set.range γ = insert (γ (Fin.last n)) (Set.range (Fin.init γ)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact Fin.lastCases (Or.inl rfl) (fun j => Or.inr ⟨j,rfl⟩) i
    · rintro (rfl | ⟨i,rfl⟩)
      · exact ⟨Fin.last n,rfl⟩
      · exact ⟨i.castSucc,rfl⟩
  simp only [adjoinGammaTuple,Section2.adjoinGamma,hr,Set.union_insert]

/-- Any finite tuple of named Gamma parameters can be abstracted to
free Gamma variables over the original mixed base, with all codes retained. -/
theorem fullGamma_tuple_abstraction (B : Base (M := M)) {n : ℕ}
    (γ : Fin n → Values.Gamma (M := M)) {α : Type} [Finite α]
    (P : (α → Values.Gamma (M := M)) → Prop)
    (hP : FullGammaSyntax.Definable (integrationGammaBase (adjoinGammaTuple B γ)) P) :
    ∃ Q : ((Fin n ⊕ α) → Values.Gamma (M := M)) → Prop,
      FullGammaSyntax.Definable (integrationGammaBase B) Q ∧
      ∀ x, Q (Sum.elim γ x) ↔ P x := by
  induction n generalizing α with
  | zero =>
    rw [adjoinGammaTuple_zero B γ] at hP
    exact ⟨fun z => P (z ∘ Sum.inr),hP.reindex Sum.inr,fun _ => Iff.rfl⟩
  | succ n ih =>
    have hPc : FullGammaSyntax.Definable
        (integrationGammaBase (Section2.adjoinGamma (adjoinGammaTuple B (Fin.init γ)) (γ (Fin.last n)))) P := by
      rwa [← adjoinGammaTuple_succ B γ]
    obtain ⟨Q1,hQ1,hQ1x⟩ := fullGamma_adjoin_abstraction (adjoinGammaTuple B (Fin.init γ)) (γ (Fin.last n)) P hPc
    obtain ⟨Q0,hQ0,hQ0x⟩ := ih (Fin.init γ) Q1 hQ1
    let e : Fin n ⊕ (Fin 1 ⊕ α) → Fin (n+1) ⊕ α :=
      Sum.elim (fun i => Sum.inl i.castSucc)
        (Sum.elim (fun _ => Sum.inl (Fin.last n)) Sum.inr)
    refine ⟨fun z => Q0 (z ∘ e),hQ0.reindex e,?_⟩
    intro x
    have he : (Sum.elim γ x) ∘ e = Sum.elim (Fin.init γ) (Sum.elim (fun _ : Fin 1 => γ (Fin.last n)) x) := by
      funext j
      cases j with
      | inl i => rfl
      | inr j =>
        cases j with
        | inl i => rfl
        | inr i => rfl
    change Q0 ((Sum.elim γ x) ∘ e) ↔ P x
    rw [he,hQ0x,hQ1x]
end DiamondIntegral.Section3
