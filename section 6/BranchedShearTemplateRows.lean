import «section 6».BranchedShearTemplateSources

/-! A positive sorted indicator row has actual VF and RV witnesses.
Thus first-order row inclusions test the entire typed chart family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BranchedShearChartTemplate
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem oneCode_row_iff (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) (z : Fin (r+s) ⊕ Fin (n+1) → M) :
    Sum.elim a z ∈ T.oneCode ↔ ∃ w : Fin (r+s) → RVInfinity M,∃ x : Fin (n+1) → VF M,
      Sum.elim (rvValues w) (vfValues x)=z ∧ T.indicator.value a ha w x 0=1 := by
  constructor
  · intro h
    have hInputs : z ∘ Sum.inl ∈ (rawRVSpace (M := M) (r+s)).domain ∧
        z ∘ Sum.inr ∈ (rawVFSpace (M := M) (n+1)).domain := h.1
    obtain ⟨w,hw⟩ := hInputs.1
    obtain ⟨x,hx⟩ := hInputs.2
    have he : Sum.elim (rvValues w) (vfValues x)=z := by
      funext i
      cases i with
      | inl i => exact congrFun hw i
      | inr i => exact congrFun hx i
    refine ⟨w,x,he,(T.oneCode_at a ha w x).mp ?_⟩
    rw [he]
    exact h
  · rintro ⟨w,x,rfl,h⟩
    exact (T.oneCode_at a ha w x).mpr h

theorem oneCode_subset_iff (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) (P : Set (Fin (r+s) ⊕ Fin (n+1) → M)) :
    a ∈ rawRowSubsetParameterLocus T.oneCode {z | z ∘ Sum.inr ∈ P} ↔
      ∀ w x,T.indicator.value a ha w x 0=1 → Sum.elim (rvValues w) (vfValues x) ∈ P := by
  rw [rawRowSubsetParameterLocus_at]
  constructor
  · intro h w x hx
    exact h _ ((T.oneCode_at a ha w x).mpr hx)
  · intro h z hz
    obtain ⟨w,x,he,hx⟩ := (T.oneCode_row_iff a ha z).mp hz
    change z ∈ P
    rw [← he]
    exact h w x hx

end DiamondIntegral.Section6.BranchedShearChartTemplate
