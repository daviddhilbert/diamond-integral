import «section 3».ACFCountableCoefficients
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CompatibleRing K]

/-- A finite family with different tuple arities still has a single
countable algebraically closed coefficient field inside the ambient field. -/
theorem acf_dependent_family_countable_algclosed_coefficients {ι : Type} [Finite ι]
    (α : ι → Type) (R : ∀ i, Set (α i → K))
    (hR : ∀ i, (Set.univ : Set K).Definable Language.ring (R i)) :
    ∃ E : Subfield K, Cardinal.mk E ≤ Cardinal.aleph0 ∧ IsAlgClosed E ∧
      ∀ i, (E : Set K).Definable Language.ring (R i) := by
  letI := Fintype.ofFinite ι
  choose C hC hD using fun i => Set.definable_iff_finitely_definable.mp (hR i)
  let D := Finset.univ.biUnion C
  obtain ⟨E,hDE,hE,hclosed⟩ := finite_parameters_countable_algclosed_subfield D
  refine ⟨E,hE,hclosed,?_⟩
  intro i
  apply (hD i).mono
  intro c hc
  apply hDE
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hc⟩

end DiamondIntegral.Section3
