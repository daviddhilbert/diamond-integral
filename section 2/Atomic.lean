import «section 2».Conventions
import Section3.GammaBaseTools
import Section3.GammaClosureLaws

/-! Definition 2.22 uses complete types throughout. All formulas are over
the indicated ground base, including genuine Gamma names. Referee notes
are not hypotheses. No atomic base-change result is postulated here. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A nonempty set whose points agree on every formula over the base. -/
def GeneratesCompleteType (B : ParameterBase M) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) : Prop :=
  A.Nonempty ∧ A ⊆ GammaParameters.sortedUniverse sn ∧
    ∀ C, GammaParameters.DefinableOverBase B sn C → A ⊆ C ∨ Disjoint A C

/-- The manuscript's complete type-definable set is maximal among sets
generating a complete type. This is not the partial-type convention. -/
def IsCompleteTypeDefinable (B : ParameterBase M) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) : Prop :=
  GeneratesCompleteType B sn A ∧
    ∀ C, A ⊆ C → GeneratesCompleteType B sn C → C ⊆ A

def IsAtomic (B : ParameterBase M) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) : Prop :=
  GammaParameters.DefinableOverBase B sn A ∧ GeneratesCompleteType B sn A

theorem GeneratesCompleteType.subset_nonempty {B : ParameterBase M} {n : ℕ}
    {sn : Fin n → SortTag} {A C : Set (Fin n → M)}
    (hA : GeneratesCompleteType B sn A) (hCA : C ⊆ A) (hne : C.Nonempty) :
    GeneratesCompleteType B sn C := by
  refine ⟨hne, hCA.trans hA.2.1, ?_⟩
  intro D hD
  rcases hA.2.2 D hD with hAD | hAD
  · exact Or.inl (hCA.trans hAD)
  · exact Or.inr (hAD.mono_left hCA)

/-- Removing parameters preserves agreement on formulas. -/
theorem GeneratesCompleteType.restrict_base {B C : ParameterBase M} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : GeneratesCompleteType C sn A) (hr : B.real ⊆ C.real)
    (hg : B.gamma ⊆ C.gamma) : GeneratesCompleteType B sn A :=
  ⟨hA.1, hA.2.1, fun D hD => hA.2.2 D (hD.mono hr hg)⟩

/-- The equivalence stated in Definition 2.22. -/
theorem isAtomic_iff_definable_completeTypeDefinable (B : ParameterBase M)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) :
    IsAtomic B sn A ↔ GammaParameters.DefinableOverBase B sn A ∧ IsCompleteTypeDefinable B sn A := by
  constructor
  · rintro ⟨hdef, hA⟩
    refine ⟨hdef, hA, ?_⟩
    intro C hAC hC
    rcases hC.2.2 A hdef with hCA | hCA
    · exact hCA
    · obtain ⟨a, ha⟩ := hA.1
      exact (Set.disjoint_left.mp hCA (hAC ha) ha).elim
  · rintro ⟨hdef, hA, _⟩
    exact ⟨hdef, hA⟩

/-- An infinite atomic set cannot meet a finite set definable over the
same base. This does not claim individual definability of algebraic points. -/
theorem IsAtomic.disjoint_finite {B : ParameterBase M} {n : ℕ}
    {sn : Fin n → SortTag} {A C : Set (Fin n → M)} (hA : IsAtomic B sn A)
    (hinf : A.Infinite) (hC : GammaParameters.DefinableOverBase B sn C) (hfin : C.Finite) :
    Disjoint A C := by
  rcases hA.2.2.2 C hC with hAC | hAC
  · exact (hinf (hfin.subset hAC)).elim
  · exact hAC

theorem IsAtomic.not_algebraic_at {B : ParameterBase M} {σ : SortTag}
    {A : Set (Fin 1 → M)} (hA : IsAtomic B (fun _ => σ) A) (hinf : A.Infinite)
    {a : Fin 1 → M} (ha : a ∈ A) :
    ¬ GammaParameters.AlgebraicAtBase B σ (a 0) := by
  rintro ⟨C, hC, hfin, hac⟩
  have heval : Function.Injective (fun z : Fin 1 → M => z 0) := by
    intro z w h
    funext i
    fin_cases i
    exact h
  have hf : {z : Fin 1 → M | z 0 ∈ C}.Finite := hfin.preimage heval.injOn
  exact Set.disjoint_left.mp (hA.disjoint_finite hinf hC hf) ha hac

/-- A genuine Gamma name is added without choosing an RV representative. -/
def adjoinGamma (B : ParameterBase M) (γ : Gamma M) : ParameterBase M :=
  ⟨B.real, insert γ B.gamma⟩

/-- Adding a name already definable over the base preserves atomicity,
including when the original value group is trivial. This elementary case
does not invoke the cited nontrivial-base result of Lemma 2.23. -/
theorem IsAtomic.adjoin_definable_gamma {B : ParameterBase M} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : IsAtomic B sn A)
    (γ : Gamma M) (hγ : GammaParameters.GammaDefinableClosureAtBase B γ) :
    IsAtomic (adjoinGamma B γ) sn A := by
  refine ⟨hA.1.mono (Set.Subset.refl _) (Set.subset_insert _ _), hA.2.1, hA.2.2.1, ?_⟩
  intro C hC
  apply hA.2.2.2 C
  apply hC.eliminate_definable_params
  · exact fun c hc => (GammaParameters.subset_closureBase B).1 hc
  · intro δ hδ
    rcases hδ with rfl | hδ
    · exact hγ
    · exact GammaParameters.gamma_name_definable B δ hδ

end DiamondIntegral.Section2
