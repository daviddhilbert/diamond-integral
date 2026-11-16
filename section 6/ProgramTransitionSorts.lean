import «section 6».CentripetalProgramTemplates

/-! Every program transition preserves the actual VF/RV sorts even
outside its geometric admissibility locus. Intermediate image templates
therefore require no additional clipping when transitions are composed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem rawMixedSpace_domain_iff (z : Fin n ⊕ Fin r → M) :
    z ∈ (rawMixedSpace (M := M) n r).domain ↔
      (∀ i,iVF (z (.inl i))) ∧ ∀ i,iRV (z (.inr i)) := by
  change ((z ∘ Sum.inl ∈ Set.range vfValues) ∧ (z ∘ Sum.inr ∈ Set.range rvValues)) ↔ _
  constructor
  · rintro ⟨⟨a,ha⟩,⟨u,hu⟩⟩
    constructor
    · intro i
      have h : (a i).val=z (.inl i) := congrFun ha i
      exact h ▸ (a i).property
    · intro i
      have h : (u i).val=z (.inr i) := congrFun hu i
      exact h ▸ (u i).property
  · rintro ⟨ha,hu⟩
    exact ⟨⟨fun i => ⟨z (.inl i),ha i⟩,rfl⟩,⟨fun i => ⟨z (.inr i),hu i⟩,rfl⟩⟩

theorem regularizeCodes_output_domain (z : Fin n ⊕ Fin r → M)
    (hz : z ∈ (rawMixedSpace (M := M) n r).domain) :
    regularizeCodes z ∈ (rawMixedSpace (M := M) n (n+r)).domain := by
  have he : mixedValues ((rawMixedSpace n r).decode ⟨z,hz⟩)=z := mixedValues_decode _
  rw [← he,regularizeCodes_at]
  exact mixedValues_mem_domain _

theorem scalarCentripetalCodes_output_domain (j : Fin n) (z : ScalarStepCodeIndex n r → M)
    (hz : (z ∘ Sum.inl) ∈ (rawMixedSpace (M := M) n r).domain)
    (hFocus : iVF (z (.inr (.inl 0)))) (hCoeff : iVF (z (.inr (.inr 0)))) :
    scalarCentripetalCodes j z ∈ (rawMixedSpace (M := M) n (1+r)).domain := by
  obtain ⟨hx,hu⟩ := (rawMixedSpace_domain_iff _).mp hz
  have hDiff : iVF (scalarStepDifference j z) := vf_add_mem hM (hx j) (vf_neg_mem hM hFocus)
  have hProd : iVF (scalarStepProduct z) := vf_mul_mem hM hCoeff hFocus
  apply (rawMixedSpace_domain_iff _).mpr
  constructor
  · intro i
    simp only [scalarCentripetalCodes,Sum.elim_inl]
    split
    · split
      · exact vf_add_mem hM hDiff hProd
      · exact hDiff
    · exact hx i
  · intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [scalarCentripetalCodes,Sum.elim_inr,Fin.append_left]
      split <;> exact (branchTag (M := M) _).property
    · simpa only [scalarCentripetalCodes,Sum.elim_inr,Fin.append_right,Function.comp_apply] using hu k

theorem FocusComponentParameterTemplate.transition_output_domain
    (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (z : Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin (1+r))) → M)
    (hz : z ∈ focusComponentTransition T A) :
    (fun i => z (.inr (.inr i))) ∈ (rawMixedSpace (M := M) n (1+r)).domain := by
  obtain ⟨hSource,w,hF,hC,hStep⟩ := hz
  have hFocus : iVF (w (.inl 0)) := by
    rcases hF with hF | hF
    · exact (T.focus.sorted _ hF.2).2 0
    · have he : w (.inl 0)=iVFZero := hF.2
      rw [he]
      exact vf_zero_mem hM
  have hCoeff : iVF (w (.inr 0)) := (T.coefficient.sorted _ hC).2 0
  have h := scalarCentripetalCodes_output_domain T.coordinate
    (Sum.elim (fun i => z (.inr (.inl i))) w) hSource.1 hFocus hCoeff
  exact hStep ▸ h

theorem CentripetalProgramTemplate.transition_output_domain
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (z : Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M)
    (hz : z ∈ (T.transition A).graph) :
    (fun i => z (.inr (.inr i))) ∈ (rawMixedSpace (M := M) n s).domain := by
  induction T with
  | identity r =>
    obtain ⟨hSource,hOut⟩ := hz
    exact hOut ▸ hSource.1
  | regularize r =>
    obtain ⟨hSource,hOut⟩ := hz
    exact hOut ▸ regularizeCodes_output_domain _ hSource.1
  | centripetal T => exact T.transition_output_domain A z hz
  | comp F H ihF ihH =>
    obtain ⟨y,hyF,hyH⟩ := hz
    exact ihH (F.target A) _ hyH

theorem CentripetalProgramTemplate.image_typedGraph
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A C : MixedSetParameterTemplate (M := M) S p n r) :
    (T.pieceTarget A C).typedGraph=(T.pieceTarget A C).graph := by
  ext z
  constructor
  · exact And.right
  · rintro ⟨x,hR,hC⟩
    exact ⟨T.transition_output_domain A _ hR,⟨x,hR,hC⟩⟩

end DiamondIntegral.Section6
