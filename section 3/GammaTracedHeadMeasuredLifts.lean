import «section 3».GammaHeadLiftForms
import IntegrationSection5.GammaProgramTraceHelper

/-! A certified head preparation and its canonical lift form a full
measured comparison with the original retained Gamma density. The proof
uses the native trace compiler, with no change of the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {U : DefSet (M := M) Set.univ (n+1) a}

theorem gammaTracedHead_full_measured_lift
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation U) (W : UniformRelativeTrace Set.univ (n+1) U T.target)
    (hWG : GammaUniformTrace (G := B) W) (hW : ∀ u, W.toMap u = T.map u)
    (hfin : ∀ x, {r | (x,r) ∈ carrier U}.Finite)
    (Q : GammaGroundDefSet hc B (SpecialTransformations.Section4.rawRVSpace (M := M) a))
    (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    let hTarget := (gammaUniformTraceIso W hWG).target_definable (gammaLogicInput B)
    let Ω := gammaPointRetainedForm U hWG.source Q id (fun u => hLabels u) ω
    let η := gammaHeadLiftForm T hTarget Q hLabels ω
    ∃ hfinH : ∀ x, {r | (x,r) ∈ carrier T.liftSet}.Finite,
    ∃ F : GammaFullMeasuredBijection
      (gammaPointMeasuredData (hc := hc) U hWG.source hfin Ω)
      (gammaPointMeasuredData T.liftSet (gamma_coordinateCanonicalImage T.target hTarget 0) hfinH η),
      ∀ p, (F.map.map p).val = (T.liftMap ⟨p.val,p.property⟩).val := by
  intro hTarget Ω η
  let H := T.liftSet
  have hH := gamma_coordinateCanonicalImage T.target hTarget 0
  let C : UniformRelativeTrace Set.univ (n+1) T.target H := .canonical 0 (.nil H)
  have hCG : GammaUniformTrace (G := B) C := ⟨hTarget,hH⟩
  let R := W.append C
  have hRG : GammaUniformTrace (G := B) R := gamma_uniform_trace_append W C hWG hCG
  have hR (u : U) : (R.toMap u).val = (T.liftMap u).val := by
    rw [UniformRelativeTrace.append_apply,hW]
    rfl
  have hForms : ∀ p, gammaGroundFormValue Ω p = gammaGroundFormValue η
      ⟨(R.toMap ⟨p.val,p.property⟩).val,(R.toMap ⟨p.val,p.property⟩).property⟩ := by
    intro p
    let u : U := ⟨p.val,p.property⟩
    have hPoint : (⟨(R.toMap u).val,(R.toMap u).property⟩ :
        Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH) =
      ⟨(T.liftMap u).val,(T.liftMap u).property⟩ := Subtype.ext (hR u)
    change gammaGroundFormValue Ω p = gammaGroundFormValue η ⟨(R.toMap u).val,(R.toMap u).property⟩
    rw [hPoint]
    exact (congrArg (fun q => cast (gammaCarrier hc) q.val)
      (gammaHeadLiftForm_apply T hTarget Q hLabels ω u)).symm
  obtain ⟨hfinH,F,hF⟩ := gammaUniformTrace_full_measured (hc := hc) hκ hs h00 hr hv R hRG hfin Ω η hForms
  exact ⟨hfinH,F,fun p => (hF p).trans (hR ⟨p.val,p.property⟩)⟩

end DiamondIntegral.Section3
