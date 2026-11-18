import «section 3».GammaUniformTraceMeasuredBijections

/-! The checked unit trace map transports any actual original-base Gamma
forms that agree along that trace. No density representative is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaUniformTrace_full_measured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (M := M) S (n+1) a} {D : DefSet (M := M) S (n+1) b}
    (T : UniformRelativeTrace S (n+1) A D) (hT : GammaUniformTrace (G := B) T)
    (hfinA : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hT.source))
    (η : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier D)
      ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B))))
    (hForm : ∀ p, gammaGroundFormValue ω p = gammaGroundFormValue η
      ⟨(T.toMap ⟨p.val,p.property⟩).val,(T.toMap ⟨p.val,p.property⟩).property⟩) :
    ∃ hfinD : ∀ x, {r | (x,r) ∈ carrier D}.Finite,
    ∃ F : GammaFullMeasuredBijection
      (gammaPointMeasuredData (hc := hc) A hT.source hfinA ω)
      (gammaPointMeasuredData D ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)) hfinD η),
      ∀ p, (F.map.map p).val = (T.toMap ⟨p.val,p.property⟩).val := by
  obtain ⟨hfinD,F,hMap⟩ := gammaUniformTrace_full_unit_measured (hc := hc) hκ hs h00 hr hv T hT hfinA
  let E : GammaFullMeasuredBijection
      (gammaPointMeasuredData (hc := hc) A hT.source hfinA ω)
      (gammaPointMeasuredData D ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)) hfinD η) := {
    map := F.map
    measure := by
      intro p hp
      obtain ⟨J,hJ,hw⟩ := F.measure p hp
      have hOne : Values.vfValueHom J = 1 := by
        simpa only [gammaGroundMeasuredVFWeight,gammaPointMeasuredData,gammaGroundOneForm_value,
          Values.gamma_val_one,one_mul] using hw.symm
      refine ⟨J,hJ,?_⟩
      rw [hOne,mul_one]
      have hTarget : (⟨(T.toMap ⟨p.val,p.property⟩).val,(T.toMap ⟨p.val,p.property⟩).property⟩ :
          Section5.nativeGammaPointDomain (hc := hc) (carrier D)
            ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B))) = F.map.map p :=
        Subtype.ext (hMap p).symm
      have h := hForm p
      rw [hTarget] at h
      exact congrArg (fun v : Values.Gamma (M := M) => v.val) h }
  exact ⟨hfinD,E,hMap⟩

end DiamondIntegral.Section3
