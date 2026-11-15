import «section 5».OriginalPredicateSyntax

/-! A parameter-free formula gives an original-Gamma predicate after its
sorted guard is imposed. Canonical totalization is transported explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem parameter_free_formula_original_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (s : Fin n → SortTag) (φ : LRV.Formula (Fin n)) :
    DefinableOverBase B s {x : Fin n → M | x ∈ sortedUniverse s ∧ φ.Realize x} := by
  apply real_definableOverBase
  apply (definableOver_iff_normalized_raw B.real s _).mpr
  have hφ : (∅ : Set M).Definable LRV {x : Fin n → M | φ.Realize x} :=
    Set.empty_definable_iff.mpr ⟨φ, rfl⟩
  have hsort := ((definableOver_iff_normalized_raw B.real s _).mp (sortedUniverse_definable B.real s)).1
  rw [canonical_normalize_eq hc] at hsort ⊢
  exact ⟨hsort.inter (hφ.mono (Set.empty_subset _)), fun _ h => h.1⟩

end DiamondIntegral.Section5
