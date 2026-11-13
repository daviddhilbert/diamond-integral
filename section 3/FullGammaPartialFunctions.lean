import «section 3».FullGammaFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure FullGammaPartialFunction (B : FullBaseAtomicity.Base (M := M)) (n : ℕ) where
  graph : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) → Prop
  definable : FullGammaSyntax.Definable B (fun z : Fin n ⊕ Fin 1 → Values.Gamma (M := M) => graph (z ∘ Sum.inl) (z (.inr 0)))
  functional : ∀ γ δ ε, graph γ δ → graph γ ε → δ = ε

namespace FullGammaPartialFunction
variable {B : FullBaseAtomicity.Base (M := M)} {n : ℕ}

def domain (D : FullGammaPartialFunction B n) : Set (Fin n → Values.Gamma (M := M)) :=
  {γ | ∃ δ, D.graph γ δ}

def eval (D : FullGammaPartialFunction B n) (γ : Fin n → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  if h : ∃ δ, D.graph γ δ then Classical.choose h else 1

theorem eval_graph (D : FullGammaPartialFunction B n) (γ : Fin n → Values.Gamma (M := M))
    (h : ∃ δ, D.graph γ δ) : D.graph γ (D.eval γ) := by
  rw [eval,dite_eq_left h]
  exact Classical.choose_spec h

theorem eval_eq (D : FullGammaPartialFunction B n) (γ : Fin n → Values.Gamma (M := M))
    (δ : Values.Gamma (M := M)) (h : D.graph γ δ) : D.eval γ = δ :=
  D.functional γ _ _ (D.eval_graph γ ⟨δ,h⟩) h

theorem domain_definable (D : FullGammaPartialFunction B n) :
    FullGammaSyntax.Definable B (fun γ => γ ∈ D.domain) := by
  apply D.definable.exists_block.congr
  intro γ
  change (∃ c : Fin 1 → Values.Gamma (M := M), D.graph γ (c 0)) ↔ ∃ δ, D.graph γ δ
  exact ⟨fun ⟨c,hc⟩ => ⟨c 0,hc⟩,fun ⟨δ,hδ⟩ => ⟨fun _ => δ,hδ⟩⟩

/-- Totalization by the definable constant one keeps the original full
Gamma-code graph and agrees with the partial function wherever defined. -/
theorem eval_definable (D : FullGammaPartialFunction B n) : FullGammaFunction B D.eval := by
  have hone := FullGammaSyntax.unary_at (FullGammaSyntax.one_definable B) (Sum.inr (0 : Fin 1) : Fin n ⊕ Fin 1)
  have hh := D.definable.or (((D.domain_definable).reindex (Sum.inl : Fin n → Fin n ⊕ Fin 1)).not.and hone)
  apply hh.congr
  intro z
  change (D.graph (z ∘ Sum.inl) (z (.inr 0)) ∨
    (¬ (∃ δ, D.graph (z ∘ Sum.inl) δ)) ∧ z (.inr 0) ∈ {(1 : Values.Gamma (M := M))}) ↔
      D.eval (z ∘ Sum.inl) = z (.inr 0)
  by_cases hx : ∃ δ, D.graph (z ∘ Sum.inl) δ
  · constructor
    · rintro (h | h)
      · exact D.eval_eq _ _ h
      · exact False.elim (h.1 hx)
    · intro he
      left
      rw [← he]
      exact D.eval_graph _ hx
  · constructor
    · rintro (h | h)
      · exact False.elim (hx ⟨_,h⟩)
      · rw [eval,dite_eq_right hx]
        exact (Set.mem_singleton_iff.mp h.2).symm
    · intro he
      rw [eval,dite_eq_right hx] at he
      exact Or.inr ⟨hx,Set.mem_singleton_iff.mpr he.symm⟩
end FullGammaPartialFunction
end DiamondIntegral.Section3
