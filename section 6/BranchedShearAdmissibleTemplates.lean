import «section 6».BranchedShearFullDiscLoci

/-! A single original-base definable parameter locus contains every
condition needed to construct actual branched shear data on the prescribed
source. Its specialization has no geometric or derivative premises. -/

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
namespace BranchedShearChartTemplate

theorem uniqueGood_expanded_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) :
    a ∈ T.uniqueGood ↔ ∀ x u v w,
      T.indicator.value a ha (Fin.append u v) x 0=1 →
      T.indicator.value a ha (Fin.append u w) x 0=1 → v=w := by
  rw [T.uniqueGood_at a ha]
  constructor
  · intro h x u v w hv hw
    have hL : T.indicator.value a ha ((Fin.append u (Fin.append v w)) ∘ pairedLeftLabels r s) x 0=1 := by
      rw [pairedLeftLabels_append]; exact hv
    have hR : T.indicator.value a ha ((Fin.append u (Fin.append v w)) ∘ pairedRightLabels r s) x 0=1 := by
      rw [pairedRightLabels_append]; exact hw
    have he := h (x,Fin.append u (Fin.append v w)) hL hR
    funext i
    have hi := congrFun he i
    simpa only [Function.comp_apply,Fin.append_right,Fin.append_left] using hi
  · intro h q hL hR
    let u := q.2 ∘ Fin.castAdd (s+s)
    let v := (q.2 ∘ Fin.natAdd r) ∘ Fin.castAdd s
    let w := (q.2 ∘ Fin.natAdd r) ∘ Fin.natAdd s
    have heL : q.2 ∘ pairedLeftLabels r s=Fin.append u v := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Function.comp_apply,pairedLeftLabels,Fin.addCases_left,Fin.addCases_right,
          Fin.append_left,Fin.append_right,u,v]
    have heR : q.2 ∘ pairedRightLabels r s=Fin.append u w := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Function.comp_apply,pairedRightLabels,Fin.addCases_left,Fin.addCases_right,
          Fin.append_left,Fin.append_right,u,w]
    rw [heL] at hL
    rw [heR] at hR
    exact h q.1 u v w hL hR

def good (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) : Set (Fin p → M) :=
  T.goodFunctions ∩ (rvScalarBinaryParameterLocus T.indicator ∩ (T.sourceGood A ∩
    (T.uniqueGood ∩ (T.retainedGood ∩ (T.nonzeroGood ∩ (T.leadingGood ∩ T.fullDiscGood))))))

theorem good_definable (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) : S.Definable LRV (T.good A) :=
  T.goodFunctions_definable.inter ((rvScalarBinaryParameterLocus_definable T.indicator).inter
    ((T.sourceGood_definable A).inter (T.uniqueGood_definable.inter
      (T.retainedGood_definable.inter (T.nonzeroGood_definable.inter
        (T.leadingGood_definable.inter T.fullDiscGood_definable))))))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def toData
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : BranchedShearChartTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) (a : Fin p → M) (ha : a ∈ T.good A) :
    BranchedShearData (G := G) (A.fibre a) where
  arity := s
  indicator := T.indicator.value a ha.1.1
  offset := T.offset.value a ha.1.2
  indicator_definable := T.indicator.family_graph_definable a ha.1.1
  offset_definable := T.offset.family_graph_definable a ha.1.2
  indicator_continuous := T.indicator.value_continuous hv a ha.1.1
  offset_continuous := T.offset.value_continuous hv a ha.1.2
  labels := T.labels
  labels_injective := T.labels_injective
  leading := T.leading
  binary := (rvScalarBinaryParameterLocus_at T.indicator a ha.1.1).mp ha.2.1
  source := by
    intro x u
    rw [← (T.sourceGood_at A a).mp ha.2.2.1]
    exact T.sourceTemplate_fibre_at a ha.1.1 x u
  unique := (T.uniqueGood_expanded_at a ha.1.1).mp ha.2.2.2.1
  retained := by
    intro x u v hx
    have h := (T.retainedGood_at a ha.1.1).mp ha.2.2.2.2.1 (Fin.append u v) x hx
    funext i
    simpa only [Function.comp_apply,Fin.append_right,Fin.append_left] using congrFun h i
  nonzero := by
    intro x u v hx i
    have h := (T.nonzeroGood_at a ha.1.1).mp ha.2.2.2.2.2.1 (Fin.append u v) x hx i
    simpa only [Fin.append_right] using h
  leading_value := by
    intro x u v hx
    have h := (T.leadingGood_at a ha.1).mp ha.2.2.2.2.2.2.1 (Fin.append u v) x hx
    simpa only [Fin.append_right] using h
  full_disc := by
    intro x u v hx d hd
    apply (T.fullDiscGood_at a ha.1).mp ha.2.2.2.2.2.2.2 (Fin.append u v) x hx d
    simpa only [Fin.append_right] using hd

end BranchedShearChartTemplate
end DiamondIntegral.Section6
