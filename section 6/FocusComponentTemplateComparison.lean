import «section 6».PromotedFocusComponentTemplates

/-! Reconstructing the promoted complete data preserves the original
component on its whole actual source, including its coefficient, focus
and branch test. Every protected component remains compatible. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FocusComponentParameterTemplate.exists_exact_component
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (a : Fin p → M) (ha : a ∈ T.good A P)
    (D : CentripetalData (G := G) (A.fibre a))
    (E : ∀ i,CentripetalData (G := G) ((P i).fibre a)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (hj : T.coordinate=D.coordinate) (hU : T.active.fibre a=D.activeTags)
    (hC : vfScalarTemplateValue T.coefficient a ha.1.1.2=D.coefficient)
    (hF : ∀ u x,T.focus.value a ha.1.1.1 u x=totalFocusFibre D.focusMap u x) :
    ∃ H : CentripetalData (G := G) (A.fibre a),ApertureRestrictionData D H ∧
      (∀ q ∈ (A.fibre a).carrier,H.point q=D.point q) ∧
        ∀ i,∃ K : CentripetalData (G := G) ((P i).fibre a),ApertureRestrictionData H K := by
  obtain ⟨H,hjH,hUH,hCH,hFocus,hPieces⟩ := T.exists_component hc hv A P a ha
    D.sourceProper D.sourceDoublyBounded (fun i => (hRestr i).subset) (fun i => (E i).sourceProper)
  have hData : ApertureRestrictionData D H := by
    refine ⟨fun _ h => h,hjH.trans hj,hCH.trans hC,?_⟩
    intro q hq
    by_cases hu : q.2 ∈ D.activeTags.carrier
    · have huT : q.2 ∈ (T.active.fibre a).carrier := by simpa only [hU] using hu
      have h := hFocus ⟨q,hq,huT⟩
      rw [hF,totalFocusFibre_at D.focusMap q.2 q.1 ⟨hq,hu⟩] at h
      exact h.trans ((D.focusMap_eq ⟨q,hq,hu⟩).trans (D.extendedFocus_active hq hu).symm)
    · have huH : q.2 ∉ H.activeTags.carrier := by simpa only [hUH,hU] using hu
      rw [H.extendedFocus_inactive huH,D.extendedFocus_inactive hu]
  exact ⟨H,hData,fun q hq => hData.point q hq,hPieces⟩

end DiamondIntegral.Section6
