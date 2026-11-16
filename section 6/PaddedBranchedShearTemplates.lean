import «section 6».RVTemplateOperationValues
import «section 6».BranchedShearTemplateSemantics

/-! Each local chart template is padded into the same output RV arity.
The source indicator is zero on invalid padded codes; the inactive offset
is pulled back by the exact local decoder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}
variable {arity : Fin k → ℕ}

theorem packedBranchLocalIndex_append (i : Fin k) (u : Fin r → RVInfinity M)
    (v : Fin (packedBranchArity r arity) → RVInfinity M) :
    Fin.append u v ∘ packedBranchLocalIndex r arity i=Fin.append u (packedBranchDecode arity i v) := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
    simp only [Function.comp_apply,packedBranchLocalIndex,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right,packedBranchDecode]

theorem packedBranchValidCode_append (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (packedBranchArity r arity) → RVInfinity M) :
    rvValues (Fin.append u v) ∈ packedBranchValidCode r arity leading i ↔
      v=packedBranchEncode arity leading i u (packedBranchDecode arity i v) := by
  rw [packedBranchValidCode_at]
  have hOld : Fin.append u v ∘ Fin.castAdd (packedBranchArity r arity)=u := by
    funext j; exact Fin.append_left u v j
  have hNew : Fin.append u v ∘ Fin.natAdd r=v := by
    funext j; exact Fin.append_right u v j
  rw [hOld,hNew]

def paddedShearTemplate
    (T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i)) (i : Fin k) :
    BranchedShearChartTemplate (M := M) S p n r (packedBranchArity r arity) where
  indicator := ((T i).indicator.reindexRV (packedBranchLocalIndex r arity i)).rvCases
    ContinuousRVGraphTemplate.zero (packedBranchValidCode r arity (fun j => (T j).leading) i)
      (packedBranchValidCode_definable arity (fun j => (T j).leading) i)
  offset := (T i).offset.reindexRV (packedBranchLocalIndex r arity i)
  labels := packedBranchOld r arity
  labels_injective := packedBranchOld_injective arity
  leading := packedBranchLeading r arity

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem paddedShearTemplate_goodFunctions
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i)) (i : Fin k)
    (a : Fin p → M) (ha : a ∈ (T i).goodFunctions) : a ∈ (paddedShearTemplate T i).goodFunctions :=
  ⟨ContinuousRVGraphTemplate.rvCases_good hv _ _ _
      (packedBranchValidCode_definable arity (fun j => (T j).leading) i) a
      ((T i).indicator.reindexRV_good hv _ a ha.1) (ContinuousRVGraphTemplate.zero_good hv a),
    (T i).offset.reindexRV_good hv _ a ha.2⟩

theorem paddedShearTemplate_indicator_value
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i)) (i : Fin k)
    (a : Fin p → M) (ha : a ∈ (T i).goodFunctions)
    (hNew : a ∈ (paddedShearTemplate T i).goodFunctions)
    (w : Fin (r+packedBranchArity r arity) → RVInfinity M) (x : Fin (n+1) → VF M) :
    (paddedShearTemplate T i).indicator.value a hNew.1 w x 0=
      if rvValues w ∈ packedBranchValidCode r arity (fun j => (T j).leading) i then
        (T i).indicator.value a ha.1 (w ∘ packedBranchLocalIndex r arity i) x 0 else 0 := by
  change (((T i).indicator.reindexRV _).rvCases ContinuousRVGraphTemplate.zero _
    (packedBranchValidCode_definable arity (fun j => (T j).leading) i)).value a hNew.1 w x 0=_
  rw [ContinuousRVGraphTemplate.rvCases_value _ _ _
    (packedBranchValidCode_definable arity (fun j => (T j).leading) i) a
    ((T i).indicator.reindexRV_good hv _ a ha.1) (ContinuousRVGraphTemplate.zero_good hv a) hNew.1]
  rw [ContinuousRVGraphTemplate.reindexRV_value _ _ a ha.1,
    ContinuousRVGraphTemplate.zero_value]
  by_cases h : rvValues w ∈ packedBranchValidCode r arity (fun j => (T j).leading) i <;>
    simp only [h,ite_true,ite_false]

theorem paddedShearTemplate_offset_value
    (T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i)) (i : Fin k)
    (a : Fin p → M) (ha : a ∈ (T i).goodFunctions)
    (hNew : a ∈ (paddedShearTemplate T i).goodFunctions)
    (w : Fin (r+packedBranchArity r arity) → RVInfinity M) (x : Fin n → VF M) :
    (paddedShearTemplate T i).offset.value a hNew.2 w x=
      (T i).offset.value a ha.2 (w ∘ packedBranchLocalIndex r arity i) x := by
  exact congrFun (congrFun
    ((T i).offset.reindexRV_value (packedBranchLocalIndex r arity i) a ha.2 hNew.2) w) x

theorem paddedShearTemplate_indicator_one_iff
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : (i : Fin k) → BranchedShearChartTemplate (M := M) S p n r (arity i)) (i : Fin k)
    (a : Fin p → M) (ha : a ∈ (T i).goodFunctions)
    (hNew : a ∈ (paddedShearTemplate T i).goodFunctions)
    (u : Fin r → RVInfinity M) (v : Fin (packedBranchArity r arity) → RVInfinity M) (x : Fin (n+1) → VF M) :
    (paddedShearTemplate T i).indicator.value a hNew.1 (Fin.append u v) x 0=1 ↔
      v=packedBranchEncode arity (fun j => (T j).leading) i u (packedBranchDecode arity i v) ∧
        (T i).indicator.value a ha.1 (Fin.append u (packedBranchDecode arity i v)) x 0=1 := by
  rw [paddedShearTemplate_indicator_value hv T i a ha hNew,
    packedBranchLocalIndex_append]
  by_cases h : rvValues (Fin.append u v) ∈ packedBranchValidCode r arity (fun j => (T j).leading) i
  · rw [if_pos h]
    exact (and_iff_right ((packedBranchValidCode_append _ i u v).mp h)).symm
  · rw [if_neg h]
    have hn := mt (packedBranchValidCode_append (fun j => (T j).leading) i u v).mpr h
    simp only [zero_ne_one,hn,false_and]

end DiamondIntegral.Section6
