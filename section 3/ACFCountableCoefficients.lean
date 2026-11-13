import «section 3».ACFDefinableRationalValues
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.SetTheory.Cardinal.Subfield
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CompatibleRing K]

/-- A finite set of field parameters lies in an algebraically closed
countable subfield of the same ambient field. -/
theorem finite_parameters_countable_algclosed_subfield (C : Finset K) :
    ∃ E : Subfield K, (C : Set K) ⊆ E ∧ Cardinal.mk E ≤ Cardinal.aleph0 ∧ IsAlgClosed E := by
  let F := Subfield.closure (C : Set K)
  let E := (algebraicClosure F K).toSubfield
  have hF : Cardinal.mk F ≤ Cardinal.aleph0 := by
    exact (Subfield.cardinalMk_closure_le_max (C : Set K)).trans
      (max_le (Cardinal.lt_aleph0_of_finite _).le le_rfl)
  have hE : Cardinal.mk E ≤ Cardinal.aleph0 := by
    exact (Algebra.IsAlgebraic.cardinalMk_le_max F (algebraicClosure F K)).trans
      (max_le hF le_rfl)
  refine ⟨E,?_,hE,?_⟩
  · intro c hc
    have hf := Subfield.subset_closure hc
    exact (algebraicClosure F K).algebraMap_mem (⟨c,hf⟩ : F)
  · change IsAlgClosed (algebraicClosure F K)
    exact IsAlgClosure.isAlgClosed F

/-- Any pure-field definable relation admits countably many
algebraically closed coefficients inside the original ambient field.
This subfield is used only in the proof, not as an enlarged ground. -/
theorem acf_definable_countable_algclosed_coefficients {ι : Type}
    (A : Set K) (R : Set (ι → K)) (hR : A.Definable Language.ring R) :
    ∃ E : Subfield K, Cardinal.mk E ≤ Cardinal.aleph0 ∧ IsAlgClosed E ∧
      (E : Set K).Definable Language.ring R := by
  obtain ⟨C,_,hC⟩ := Set.definable_iff_finitely_definable.mp hR
  obtain ⟨E,hCE,hE,hclosed⟩ := finite_parameters_countable_algclosed_subfield C
  exact ⟨E,hE,hclosed,hC.mono hCE⟩

end DiamondIntegral.Section3
