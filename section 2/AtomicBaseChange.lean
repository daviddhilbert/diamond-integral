import «section 2».Atomic

/-! Lemma 2.23, relative to the author's accepted cited input [18,
Lemma 3.3]. The nontriviality condition explicitly records the manuscript's
approved standing ground-base assumption.
The input is explicit, not a new global logical principle. This module
does not assert base change for unnamed disc-imaginary parameters. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Two distinct Gamma values definable over the ground base. This states
nontriviality using actual quotient values, without selecting RV lifts.
For a language-substructure base, a bridge from its own nontrivial value
group must supply these definable names. -/
def NontrivialDefinableGamma (B : ParameterBase M) : Prop :=
  ∃ γ δ : Gamma M, GammaParameters.GammaDefinableClosureAtBase B γ ∧
    GammaParameters.GammaDefinableClosureAtBase B δ ∧ γ ≠ δ

theorem nontrivialDefinableGamma_of_names (B : ParameterBase M)
    (γ δ : Gamma M) (hγ : γ ∈ B.gamma) (hδ : δ ∈ B.gamma) (hne : γ ≠ δ) :
    NontrivialDefinableGamma B :=
  ⟨γ, δ, GammaParameters.gamma_name_definable B γ hγ,
    GammaParameters.gamma_name_definable B δ hδ, hne⟩

/-- Enlarging the named base preserves its nontrivial definable value group. -/
theorem NontrivialDefinableGamma.mono {B C : ParameterBase M}
    (hΓ : NontrivialDefinableGamma B) (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) :
    NontrivialDefinableGamma C := by
  obtain ⟨γ, δ, hγ, hδ, hne⟩ := hΓ
  exact ⟨γ, δ, GammaParameters.GammaDefinableOverBase.mono hγ hr hg,
    GammaParameters.GammaDefinableOverBase.mono hδ hr hg, hne⟩

/-- The type-preservation part of [18, Lemma 3.3], with its standing
nontriviality hypothesis. Ground definability of the atomic set is retained
by an elementary parameter-extension step in `lemma_2_23` below.

This cited input has not been independently proved in the present project.
The author has authorized treating results of [18] as given while that
paper's formalization proceeds. -/
def AtomicGammaBaseChangeInput (B : ParameterBase M) : Prop :=
  NontrivialDefinableGamma B →
    ∀ (n : ℕ) (sn : Fin n → SortTag) (A : Set (Fin n → M)),
      IsAtomic B sn A → ∀ γ : Gamma M,
        GeneratesCompleteType (adjoinGamma B γ) sn A

/-- Lemma 2.23 relative to its explicit author-accepted cited input.
The source's standing nontriviality hypothesis remains visible in the type. -/
theorem lemma_2_23 (B : ParameterBase M) (cited : AtomicGammaBaseChangeInput B)
    (hΓ : NontrivialDefinableGamma B) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) (hA : IsAtomic B sn A) (γ : Gamma M) :
    IsAtomic (adjoinGamma B γ) sn A :=
  ⟨hA.1.mono (Set.Subset.refl _) (Set.subset_insert _ _), cited hΓ n sn A hA γ⟩

end DiamondIntegral.Section2
