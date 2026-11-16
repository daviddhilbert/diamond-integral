import «section 6».BranchedShearCommonFreezing
import «section 6».CoordinateFibreTemplates

/-! The semantic part of head-parameter fusion. A common replacement
of the inactive head preserves all branch conditions once its joint
chart graphs and continuity have been established. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem ContinuousRVGraphTemplate.value_parameter_congr {p R N m : ℕ}
    (T : ContinuousRVGraphTemplate (M := M) S p R N m) {a b : Fin p → M}
    (ha : a ∈ T.good) (hb : b ∈ T.good) (he : a=b) : T.value a ha=T.value b hb := by
  cases he
  rfl

def headReparametrizedIndicator (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) (ρ : VF M → VF M)
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+2) → VF M) : Fin 1 → VF M :=
  T.indicator.value (fun _ => (ρ (x 0)).val) (hF _).1 w (Fin.tail x)

def headReparametrizedOffset (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) (ρ : VF M → VF M)
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+1) → VF M) : Fin 1 → VF M :=
  T.offset.value (fun _ => (ρ (x 0)).val) (hF _).2 w (Fin.tail x)

theorem headReparametrizedOffset_init (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) (ρ : VF M → VF M)
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+2) → VF M) :
    headReparametrizedOffset T hF ρ w (Fin.init x)=
      T.offset.value (fun _ => (ρ (x 0)).val) (hF _).2 w (Fin.init (Fin.tail x)) := by
  unfold headReparametrizedOffset
  rw [Fin.tail_init_eq_init_tail]
  rfl

theorem headReparametrizedIndicator_update_last (T : BranchedShearChartTemplate (M := M) S 1 n r s)
    (hF : ∀ a,a ∈ T.goodFunctions) (ρ : VF M → VF M)
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+2) → VF M) (c : VF M) :
    headReparametrizedIndicator T hF ρ w (Function.update x (Fin.last (n+1)) c)=
      T.indicator.value (fun _ => (ρ (x 0)).val) (hF _).1 w
        (Function.update (Fin.tail x) (Fin.last n) c) := by
  have h0 : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_zero,Fin.val_last] at he
    omega
  have hParam : (fun _ : Fin 1 => (ρ (Function.update x (Fin.last (n+1)) c 0)).val)=
      (fun _ : Fin 1 => (ρ (x 0)).val) := by
    rw [Function.update_of_ne h0]
  unfold headReparametrizedIndicator
  rw [T.indicator.value_parameter_congr (hF _).1 (hF _).1 hParam]
  have hLast : Fin.last (n+1)=(Fin.last n).succ := rfl
  rw [hLast,Fin.tail_update_succ]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def branchedShearDataOfHeadCharts
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions)
    (hGood : ∀ a : VF M,(fun _ => a.val) ∈ T.good (headFibreTemplate A))
    (ρ : VF M → VF M)
    (hSource : ∀ x u,(x,u) ∈ A.carrier ↔ (Fin.cons (ρ (x 0)) (Fin.tail x),u) ∈ A.carrier)
    (hIDef : S.Definable LRV (rvVFGraph (headReparametrizedIndicator T hF ρ)))
    (hODef : S.Definable LRV (rvVFGraph (headReparametrizedOffset T hF ρ)))
    (hICont : ∀ w,Continuous (headReparametrizedIndicator T hF ρ w))
    (hOCont : ∀ w,Continuous (headReparametrizedOffset T hF ρ w)) : BranchedShearData (G := G) A where
  arity := s
  indicator := headReparametrizedIndicator T hF ρ
  offset := headReparametrizedOffset T hF ρ
  indicator_definable := hIDef
  offset_definable := hODef
  indicator_continuous := hICont
  offset_continuous := hOCont
  labels := T.labels
  labels_injective := T.labels_injective
  leading := T.leading
  binary w x := (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).binary w (Fin.tail x)
  source := by
    intro x u
    rw [hSource x u,← mem_headFibreTemplate_iff A (ρ (x 0)) (Fin.tail x,u)]
    exact (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).source (Fin.tail x) u
  unique := by
    intro x u v w hx hw
    exact (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).unique (Fin.tail x) u v w hx hw
  retained := by
    intro x u v hx
    exact (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).retained (Fin.tail x) u v hx
  nonzero := by
    intro x u v hx
    exact (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).nonzero (Fin.tail x) u v hx
  leading_value := by
    intro x u v hx
    rw [headReparametrizedOffset_init]
    exact (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).leading_value (Fin.tail x) u v hx
  full_disc := by
    intro x u v hx d hd
    rw [headReparametrizedIndicator_update_last,headReparametrizedOffset_init]
    exact (T.toData hv (headFibreTemplate A) _ (hGood (ρ (x 0)))).full_disc (Fin.tail x) u v hx d hd

end DiamondIntegral.Section6
