import «section 6».HeadBranchedShearSemantics
import «section 6».ZeroTailSections
import «section 6».CarriedCoordinateRadii
import «section 6».RootFreezingGeometry

/-! The two repaired charts use exactly the same replaced head.
Restricting the repaired full offset to the zero section recovers its
actual inactive-coordinate function, with no change to its values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem frozenHeadIndicator_value
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (D : FMT.FocusFreezingData (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S))
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+2) → VF M) :
    totalFocusFibre (D.frozenMap (T.headIndicatorMap hF)) w x=
      headReparametrizedIndicator T hF (FMT.vfFamilyFreeze D.balls D.centers) w x := by
  rw [totalFocusFibre_at _ w x (Set.mem_univ _)]
  let c := FMT.vfFamilyFreeze D.balls D.centers (x 0)
  change (T.headIndicatorMap hF ⟨(Function.update x 0 c,w),Set.mem_univ _⟩).val=_
  rw [T.headIndicatorMap_value]
  have hParam : (fun _ : Fin 1 => (Function.update x 0 c 0).val)=(fun _ : Fin 1 => c.val) := by
    funext i
    exact congrArg Subtype.val (Function.update_self 0 c x)
  rw [T.indicator.value_parameter_congr (hF _).1 (hF _).1 hParam,Fin.tail_update_zero]
  rfl

theorem frozenHeadFullOffset_value
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (D : FMT.FocusFreezingData (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S))
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+2) → VF M) :
    totalFocusFibre (D.frozenMap (T.headFullOffsetMap hF)) w x=
      headReparametrizedOffset T hF (FMT.vfFamilyFreeze D.balls D.centers) w (Fin.init x) := by
  rw [totalFocusFibre_at _ w x (Set.mem_univ _)]
  let c := FMT.vfFamilyFreeze D.balls D.centers (x 0)
  change (T.headOffsetMap hF ⟨(Fin.init (Function.update x 0 c),w),Set.mem_univ _⟩).val=_
  have hInit : Fin.init (Function.update x 0 c)=Function.update (Fin.init x) 0 c :=
    init_update_castSucc x (0 : Fin (n+1)) c
  rw [hInit,T.headOffsetMap_value]
  have hParam : (fun _ : Fin 1 => (Function.update (Fin.init x) 0 c 0).val)=(fun _ : Fin 1 => c.val) := by
    funext i
    exact congrArg Subtype.val (Function.update_self 0 c (Fin.init x))
  rw [T.offset.value_parameter_congr (hF _).2 (hF _).2 hParam,Fin.tail_update_zero]
  rfl

theorem frozenHeadInactiveOffset_value
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (D : FMT.FocusFreezingData (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S))
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+1) → VF M) :
    totalFocusFibre (inactiveScalarRestriction (D.frozenMap (T.headFullOffsetMap hF))) w x=
      headReparametrizedOffset T hF (FMT.vfFamilyFreeze D.balls D.centers) w x := by
  rw [inactiveScalarRestriction_value,frozenHeadFullOffset_value,Fin.init_snoc]

theorem frozenHead_source_preserved
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (D : FMT.FocusFreezingData (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S))
    (hA : ∀ E : D.balls,FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (x : Fin (n+2) → VF M) (u : Fin r → RVInfinity M) :
    (x,u) ∈ A.carrier ↔
      (Fin.cons (FMT.vfFamilyFreeze D.balls D.centers (x 0)) (Fin.tail x),u) ∈ A.carrier := by
  have h := FMT.mixedFamilyFreeze_mem_iff D.balls D.centers 0 D.separated A.carrier hA (x,u)
  have hUpdate : Function.update x 0 (FMT.vfFamilyFreeze D.balls D.centers (x 0))=
      Fin.cons (FMT.vfFamilyFreeze D.balls D.centers (x 0)) (Fin.tail x) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Function.update_self,Fin.cons_zero]
    · simp only [Function.update_of_ne (Fin.succ_ne_zero j),Fin.cons_succ,Fin.tail]
  change (Function.update x 0 (FMT.vfFamilyFreeze D.balls D.centers (x 0)),u) ∈ A.carrier ↔ (x,u) ∈ A.carrier at h
  rw [hUpdate] at h
  exact h.symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def branchedShearDataOfCommonFreezing
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (hGood : ∀ a : VF M,(fun _ => a.val) ∈ T.good (headFibreTemplate A))
    (D : FMT.FocusFreezingData (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S))
    (hICont : ∀ w,Continuous (FMT.focusFibre (D.frozenMap (T.headIndicatorMap hF)) w))
    (hOCont : ∀ w,Continuous (FMT.focusFibre (D.frozenMap (T.headFullOffsetMap hF)) w))
    (hA : ∀ E : D.balls,FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) :
    BranchedShearData (G := G) A := by
  have hIEq : totalFocusFibre (D.frozenMap (T.headIndicatorMap hF))=
      headReparametrizedIndicator T hF (FMT.vfFamilyFreeze D.balls D.centers) :=
    funext (fun w => funext (frozenHeadIndicator_value T hF D w))
  have hOEq : totalFocusFibre (inactiveScalarRestriction (D.frozenMap (T.headFullOffsetMap hF)))=
      headReparametrizedOffset T hF (FMT.vfFamilyFreeze D.balls D.centers) :=
    funext (fun w => funext (frozenHeadInactiveOffset_value T hF D w))
  apply branchedShearDataOfHeadCharts hv A T hF hGood (FMT.vfFamilyFreeze D.balls D.centers)
    (frozenHead_source_preserved A D hA)
  · rw [← hIEq]
    exact totalFocusFibre_family_definable _
  · rw [← hOEq]
    exact totalFocusFibre_family_definable _
  · rw [← hIEq]
    exact fun w => totalFocusFibre_univ_continuous _ w (hICont w)
  · rw [← hOEq]
    exact fun w => inactiveScalarRestriction_continuous _ w (totalFocusFibre_univ_continuous _ w (hOCont w))

end DiamondIntegral.Section6
