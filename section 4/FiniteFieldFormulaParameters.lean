import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Algebra.Field.Basic

/-! A finite collection of definable field sets and relation graphs
admits one common finite tuple of field parameters. The variable arities
may differ across that collection. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FiniteFieldFormulaParameters

theorem common_parameters {K : Type*} {I : Type*} [Field K]
    [FirstOrder.Ring.CompatibleRing K] [Finite I] (α : I → Type*)
    (D : ∀ i, Set (α i → K)) (hD : ∀ i, (Set.univ : Set K).Definable Language.ring (D i)) :
    ∃ A : Finset K, ∀ i, (A : Set K).Definable Language.ring (D i) := by
  letI := Fintype.ofFinite I
  choose A hA hdef using fun i => Set.definable_iff_finitely_definable.mp (hD i)
  let S := Finset.univ.biUnion A
  refine ⟨S, fun i => (hdef i).mono ?_⟩
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

theorem common_formulas {K : Type*} {I : Type*} [Field K]
    [FirstOrder.Ring.CompatibleRing K] [Finite I] (α : I → Type*)
    (D : ∀ i, Set (α i → K)) (hD : ∀ i, (Set.univ : Set K).Definable Language.ring (D i)) :
    ∃ A : Finset K, ∃ φ : ∀ i, Language.ring.Formula (A ⊕ α i),
      ∀ i x, (φ i).Realize (Sum.elim (fun a : A => a.val) x) ↔ x ∈ D i := by
  obtain ⟨A, hA⟩ := common_parameters α D hD
  choose φ hφ using fun i => Set.definable_iff_exists_formula_sum.mp (hA i)
  refine ⟨A, φ, fun i x => ?_⟩
  rw [hφ i]
  rfl

end DiamondIntegral.Section4.FiniteFieldFormulaParameters
