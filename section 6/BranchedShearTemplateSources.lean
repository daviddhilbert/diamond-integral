import «section 6».BranchedShearChartTemplates
import «section 6».BinaryRVTemplateLoci
import «section 6».RawParameterRelations

/-! The source selected by a whole indicator graph is a genuine
mixed parameter template. Equality with the prescribed original source
is first-order, and its specialization has the exact typed RV semantics. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem rvValues_append (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    rvValues (Fin.append u v)=Fin.append (rvValues u) (rvValues v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [rvValues,Fin.append_left]
  · simp only [rvValues,Fin.append_right]

def branchedSourceIndex (p n r s : ℕ) :
    Fin p ⊕ (Fin (r+s) ⊕ Fin (n+1)) → (Fin p ⊕ (Fin (n+1) ⊕ Fin r)) ⊕ Fin s :=
  Sum.elim (Sum.inl ∘ Sum.inl)
    (Sum.elim (Fin.addCases (fun i => .inl (.inr (.inr i))) Sum.inr) (fun i => .inl (.inr (.inl i))))

theorem branchedSourceIndex_at (a : Fin p → M) (x : Fin (n+1) → M) (u : Fin r → M) (v : Fin s → M) :
    Sum.elim (Sum.elim a (Sum.elim x u)) v ∘ branchedSourceIndex p n r s=
      Sum.elim a (Sum.elim (Fin.append u v) x) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    cases i with
    | inl i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Function.comp_apply,branchedSourceIndex,Sum.elim_inr,Fin.addCases_left,Sum.elim_inl,Fin.append_left]
      · simp only [Function.comp_apply,branchedSourceIndex,Sum.elim_inr,Sum.elim_inl,Fin.addCases_right,Fin.append_right]
    | inr i => rfl

namespace BranchedShearChartTemplate

def oneCode (T : BranchedShearChartTemplate (M := M) S p n r s) :
    Set (Fin p ⊕ (Fin (r+s) ⊕ Fin (n+1)) → M) :=
  rvVFTemplateInputs (M := M) p (r+s) (n+1) ∩ rvScalarTemplateLevel T.indicator iVFOne

theorem oneCode_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.oneCode :=
  rvVFTemplateInputs_definable.inter (rvScalarTemplateLevel_definable T.indicator iVFOne rawVFOne_constant_definable)

theorem oneCode_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) (w : Fin (r+s) → RVInfinity M) (x : Fin (n+1) → VF M) :
    Sum.elim a (Sum.elim (rvValues w) (vfValues x)) ∈ T.oneCode ↔ T.indicator.value a ha w x 0=1 := by
  have hInput : Sum.elim a (Sum.elim (rvValues w) (vfValues x)) ∈ rvVFTemplateInputs (M := M) p (r+s) (n+1) :=
    ⟨⟨w,rfl⟩,⟨x,rfl⟩⟩
  constructor
  · intro h
    exact Subtype.ext ((rvScalarTemplateLevel_at T.indicator a ha w x iVFOne).mp h.2)
  · intro h
    exact ⟨hInput,(rvScalarTemplateLevel_at T.indicator a ha w x iVFOne).mpr (congrArg Subtype.val h)⟩

def sourceTemplate (T : BranchedShearChartTemplate (M := M) S p n r s) :
    MixedSetParameterTemplate (M := M) S p (n+1) r where
  graph := {z | ∃ v : Fin s → M,Sum.elim z v ∘ branchedSourceIndex p n r s ∈ T.oneCode}
  definable := (T.oneCode_definable.preimage_comp (branchedSourceIndex p n r s)).exists_of_finite

theorem sourceTemplate_code_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (x : Fin (n+1) → M) (u : Fin r → M) :
    Sum.elim a (Sum.elim x u) ∈ T.sourceTemplate.graph ↔
      ∃ v : Fin s → M,Sum.elim a (Sum.elim (Fin.append u v) x) ∈ T.oneCode := by
  change (∃ v : Fin s → M,Sum.elim (Sum.elim a (Sum.elim x u)) v ∘ branchedSourceIndex p n r s ∈ T.oneCode) ↔ _
  simp only [branchedSourceIndex_at]

theorem sourceTemplate_fibre_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) (x : Fin (n+1) → VF M) (u : Fin r → RVInfinity M) :
    (x,u) ∈ (T.sourceTemplate.fibre a).carrier ↔
      ∃ v : Fin s → RVInfinity M,T.indicator.value a ha (Fin.append u v) x 0=1 := by
  change Sum.elim a (Sum.elim (vfValues x) (rvValues u)) ∈ T.sourceTemplate.graph ↔ _
  rw [T.sourceTemplate_code_at]
  constructor
  · rintro ⟨vCode,hv⟩
    have hRV : Fin.append (rvValues u) vCode ∈ (rawRVSpace (M := M) (r+s)).domain := hv.1.1
    obtain ⟨w,hw⟩ := hRV
    let v : Fin s → RVInfinity M := fun i => w (Fin.natAdd r i)
    have hCode : rvValues v=vCode := by
      funext i
      have h := congrFun hw (Fin.natAdd r i)
      simpa only [rvValues,Fin.append_right,v] using h
    have hTyped : Sum.elim a (Sum.elim (rvValues (Fin.append u v)) (vfValues x)) ∈ T.oneCode := by
      rw [rvValues_append,hCode]
      exact hv
    exact ⟨v,(T.oneCode_at a ha (Fin.append u v) x).mp hTyped⟩
  · rintro ⟨v,hv⟩
    refine ⟨rvValues v,?_⟩
    have h := (T.oneCode_at a ha (Fin.append u v) x).mpr hv
    rwa [rvValues_append] at h

def sourceGood (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) : Set (Fin p → M) :=
  rawRowEqualParameterLocus T.sourceTemplate.typedGraph A.typedGraph

theorem sourceGood_definable (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) : S.Definable LRV (T.sourceGood A) :=
  rawRowEqualParameterLocus_definable _ _ T.sourceTemplate.typedGraph_definable A.typedGraph_definable

theorem sourceGood_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) (a : Fin p → M) :
    a ∈ T.sourceGood A ↔ T.sourceTemplate.fibre a=A.fibre a := by
  change a ∈ rawRowEqualParameterLocus T.sourceTemplate.typedGraph A.typedGraph ↔ _
  rw [rawRowEqualParameterLocus_at]
  constructor
  · intro h
    apply defSet_eq_of_carrier_eq
    apply (rawMixedSpace (M := M) (n+1) r).preimage_injective
    rw [T.sourceTemplate.fibre_code,A.fibre_code]
    exact h
  · intro h
    have hCode := congrArg (fun B : DefSet (rawMixedSpace (M := M) (n+1) r) (S ∪ Set.range a) =>
      (rawMixedSpace (M := M) (n+1) r).preimage B.carrier) h
    rw [T.sourceTemplate.fibre_code,A.fibre_code] at hCode
    exact hCode

end BranchedShearChartTemplate
end DiamondIntegral.Section6
