import «section 6».ScalarRVTemplateLevels

/-! Inclusion and equality of complete raw parameter rows are
first-order conditions, independently of the finite tuple indexing. -/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {ι κ : Type} [Finite ι] [Finite κ]

def rawRowSubsetParameterLocus (R Q : Set (ι ⊕ κ → M)) : Set (ι → M) :=
  forallRawParameterLocus (Rᶜ ∪ Q)

theorem rawRowSubsetParameterLocus_definable
    (R Q : Set (ι ⊕ κ → M)) (hR : S.Definable LRV R) (hQ : S.Definable LRV Q) :
    S.Definable LRV (rawRowSubsetParameterLocus R Q) :=
  forallRawParameterLocus_definable _ (hR.compl.union hQ)

theorem rawRowSubsetParameterLocus_at (R Q : Set (ι ⊕ κ → M)) (a : ι → M) :
    a ∈ rawRowSubsetParameterLocus R Q ↔ ∀ z,Sum.elim a z ∈ R → Sum.elim a z ∈ Q := by
  change (∀ z,Sum.elim a z ∉ R ∨ Sum.elim a z ∈ Q) ↔ _
  constructor
  · intro h z hz
    exact (h z).resolve_left (not_not.mpr hz)
  · intro h z
    by_cases hz : Sum.elim a z ∈ R
    · exact Or.inr (h z hz)
    · exact Or.inl hz

def rawRowEqualParameterLocus (R Q : Set (ι ⊕ κ → M)) : Set (ι → M) :=
  rawRowSubsetParameterLocus R Q ∩ rawRowSubsetParameterLocus Q R

theorem rawRowEqualParameterLocus_definable
    (R Q : Set (ι ⊕ κ → M)) (hR : S.Definable LRV R) (hQ : S.Definable LRV Q) :
    S.Definable LRV (rawRowEqualParameterLocus R Q) :=
  (rawRowSubsetParameterLocus_definable R Q hR hQ).inter (rawRowSubsetParameterLocus_definable Q R hQ hR)

theorem rawRowEqualParameterLocus_at (R Q : Set (ι ⊕ κ → M)) (a : ι → M) :
    a ∈ rawRowEqualParameterLocus R Q ↔ {z | Sum.elim a z ∈ R}={z | Sum.elim a z ∈ Q} := by
  change (a ∈ rawRowSubsetParameterLocus R Q ∧ a ∈ rawRowSubsetParameterLocus Q R) ↔ _
  rw [rawRowSubsetParameterLocus_at,rawRowSubsetParameterLocus_at]
  constructor
  · rintro ⟨hRQ,hQR⟩
    exact Set.Subset.antisymm hRQ hQR
  · intro h
    exact ⟨fun z hz => (Set.ext_iff.mp h z).mp hz,fun z hz => (Set.ext_iff.mp h z).mpr hz⟩

end DiamondIntegral.Section6
