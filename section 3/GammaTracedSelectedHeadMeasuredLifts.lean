import «section 3».GammaSelectedTraceMeasuredMaps
import «section 3».GammaHeadLiftForms
import IntegrationSection5.GammaProgramTraceHelper

/-! A traced unary head preparation with selected RV volumes gives a
full Gamma-measured map on their VF realizations. It retains the actual
canonical head map, all RV labels and every added VF tail coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : DefSet (M := M) Set.univ 1 a}

theorem gammaTracedSelectedHead_full_measured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation A) (W : UniformRelativeTrace Set.univ 1 A T.target)
    (hWG : GammaUniformTrace (G := B) W) (hW : ∀ u, W.toMap u = T.map u)
    (ρ : Fin k → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : A, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    let hTarget := (gammaUniformTraceIso W hWG).target_definable (gammaLogicInput B)
    let hH := gamma_coordinateCanonicalImage T.target hTarget 0
    let Ω := gammaPointRetainedForm A hWG.source Q id (fun u => hLabels u) ω
    let η := gammaHeadLiftForm T hTarget Q hLabels ω
    ∃ hfinH : ∀ x t, {r | (x,r) ∈ carrier T.liftSet ∧ r ∘ headSelectedLabelIndex T ρ = t}.Finite,
    ∃ F : GammaFullMeasuredBijection (gammaSelectedVFTailMeasuredData A ρ hWG.source hfin Ω)
      (gammaSelectedVFTailMeasuredData T.liftSet (headSelectedLabelIndex T ρ) hH hfinH η),
      ∀ p, (F.map.map p).val =
        (Fin.append (T.liftMap ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hWG.source p⟩).val.1
          (p.val.1 ∘ Fin.natAdd 1),
         (T.liftMap ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hWG.source p⟩).val.2) := by
  intro hTarget hH Ω η
  let C : UniformRelativeTrace Set.univ 1 T.target T.liftSet := .canonical 0 (.nil T.liftSet)
  have hCG : GammaUniformTrace (G := B) C := ⟨hTarget,hH⟩
  let R := W.append C
  have hRG := gamma_uniform_trace_append W C hWG hCG
  have hR (u : A) : (R.toMap u).val = (T.liftMap u).val := by
    rw [UniformRelativeTrace.append_apply,hW]
    rfl
  have hRetained (u : A) : (R.toMap u).val.2 ∘ headSelectedLabelIndex T ρ = u.val.2 ∘ ρ := by
    rw [hR u]
    have hRV := congrArg Prod.snd (T.lifting_square u)
    have hOld := gammaHeadContractedOldLabels T u
    funext j
    exact (congrFun hRV (headSelectedLabelIndex T ρ j)).trans (congrFun hOld (ρ j))
  have hfinH := finite_selected_rv_fibres_of_gammaIso hκ hs hr (gammaUniformTraceIso R hRG)
    ρ (headSelectedLabelIndex T ρ) hRetained hfin
  have hForms : ∀ p, Ω p = η ((Section5.nativeGammaPointBijection hRG.source
      ((gammaUniformTraceIso R hRG).target_definable (gammaLogicInput B)) (gammaUniformTraceIso R hRG)).map p) := by
    intro p
    let u : A := ⟨p.val,p.property⟩
    have hPoint : (Section5.nativeGammaPointBijection hRG.source
        ((gammaUniformTraceIso R hRG).target_definable (gammaLogicInput B)) (gammaUniformTraceIso R hRG)).map p =
        (⟨(T.liftMap u).val,(T.liftMap u).property⟩ : Section5.nativeGammaPointDomain (hc := hc) (carrier T.liftSet) hH) := by
      apply Subtype.ext
      exact (Section5.nativeGammaPointBijection_apply hRG.source
        ((gammaUniformTraceIso R hRG).target_definable (gammaLogicInput B)) (gammaUniformTraceIso R hRG) p).trans (hR u)
    rw [hPoint]
    exact (gammaHeadLiftForm_apply T hTarget Q hLabels ω u).symm
  let F := gammaSelectedTraceFullMeasured hκ hs hr hv R hRG ρ (headSelectedLabelIndex T ρ) hRetained hfin hfinH Ω η hForms
  refine ⟨hfinH,F,?_⟩
  intro p
  let u : A := ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hWG.source p⟩
  have hValue := gammaSelectedVFTailBijection_value A ρ hRG.source (headSelectedLabelIndex T ρ)
    ((gammaUniformTraceIso R hRG).target_definable (gammaLogicInput B)) R.toMap R.bijective (GammaUniformTrace.graph R hRG) hRetained p
  exact hValue.trans (congrArg (fun z => (Fin.append z.1 (p.val.1 ∘ Fin.natAdd 1),z.2)) (hR u))

end DiamondIntegral.Section3
