import «section 6».SelectedBranchedShearTemplates
import «section 6».UncurriedFamilyMapValues
import «section 6».FiniteFamilyFocusFreezing

/-! The uniformly selected chart pair gives actual original-base joint
maps. The offset ignores the active last coordinate, and both maps have
continuous fibres in the remaining tail at each fixed head. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BranchedShearChartTemplate
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

def headIndicatorMap (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S) (DefSet.univ (rawVFSpace 1) S) :=
  uncurriedFamilyMap T.indicator _ (fun x _ => (hF (fun _ => (x.1 0).val)).1)

def headOffsetMap (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+1) (r+s)) S) (DefSet.univ (rawVFSpace 1) S) :=
  uncurriedFamilyMap T.offset _ (fun x _ => (hF (fun _ => (x.1 0).val)).2)

def headFullOffsetMap (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S) (DefSet.univ (rawVFSpace 1) S) :=
  (T.headOffsetMap hF).comp (vfDropLast _)

theorem headIndicatorMap_value (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions)
    (p : DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S) :
    (T.headIndicatorMap hF p).val=
      T.indicator.value _ (hF (fun _ => (p.val.1 0).val)).1 p.val.2 (Fin.tail p.val.1) :=
  uncurriedFamilyMap_value _ _ _ p

theorem headOffsetMap_value (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions)
    (p : DefSet.univ (rawMixedSpace (M := M) (n+1) (r+s)) S) :
    (T.headOffsetMap hF p).val=
      T.offset.value _ (hF (fun _ => (p.val.1 0).val)).2 p.val.2 (Fin.tail p.val.1) :=
  uncurriedFamilyMap_value _ _ _ p

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem headIndicatorMap_tail_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (u : Fin (r+s) → RVInfinity M) (a : VF M) :
    Continuous (focusTailMap (T.headIndicatorMap hF) u a) :=
  uncurriedFamilyMap_tail_continuous hv _ _ _ u a

theorem headFullOffsetMap_tail_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (u : Fin (r+s) → RVInfinity M) (a : VF M) :
    Continuous (focusTailMap (T.headFullOffsetMap hF) u a) := by
  have he : focusTailMap (T.headFullOffsetMap hF) u a=
      fun x => T.offset.value (fun _ => a.val) (hF (fun _ => a.val)).2 u (Fin.init x.val) := by
    funext x
    change (T.headOffsetMap hF ⟨(Fin.init (Fin.cons a x.val : Fin (n+2) → VF M),u),Set.mem_univ _⟩).val=_
    rw [T.headOffsetMap_value]
    have hHead : Fin.init (Fin.cons a x.val : Fin (n+2) → VF M) 0=a := rfl
    have hTail : Fin.tail (Fin.init (Fin.cons a x.val : Fin (n+2) → VF M))=Fin.init x.val := by funext i; rfl
    rw [hTail]
    rfl
  rw [he]
  apply (T.offset.value_continuous hv _ (hF (fun _ => a.val)).2 u).comp
  exact continuous_pi (fun i => (continuous_apply i.castSucc).comp continuous_subtype_val)

end DiamondIntegral.Section6.BranchedShearChartTemplate
