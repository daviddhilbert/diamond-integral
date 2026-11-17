import «section 3».GammaTracedSelectedHeadMeasuredLifts
import «section 3».GammaHeadSelectedNativeMeasuredBridge

/-! The original unary selected family is fully Gamma-measured
isomorphic to the native lift of its raw head-contraction object.
The actual canonical head map and every selected VF tail are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {A : DefSet (M := M) Set.univ 1 a}

theorem gammaUnarySelectedHead_native_bridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : HeadPreparation A) (W : UniformRelativeTrace Set.univ 1 A T.target)
    (hWG : GammaUniformTrace (G := B) W) (hW : ∀ u, W.toMap u = T.map u)
    (ρ : Fin k → Fin a)
    (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (P : GammaFiniteGraphPresentation B (1+T.arity) (1+k)
      {r | (Fin.elim0,r) ∈ carrier T.contractedSet}
      (fun r y => (Fin.elim0,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T ρ = y))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hLabels : ∀ u : A, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    ∃ F : GammaFullMeasuredBijection
      (gammaSelectedVFTailMeasuredData A ρ hWG.source hfin
        (gammaPointRetainedForm A hWG.source Q id (fun u => hLabels u) ω))
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (gammaHeadSelectedNativeForm T ρ P Q hLabels ω)),
      ∀ p, (F.map.map p).val =
        (Fin.append (T.liftMap ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hWG.source p⟩).val.1
          (p.val.1 ∘ Fin.natAdd 1),
         (T.liftMap ⟨(p.val.1 ∘ Fin.castAdd k,p.val.2),gammaSelectedVFTail_prefix_mem A ρ hWG.source p⟩).val.2) := by
  let hTarget := (gammaUniformTraceIso W hWG).target_definable (gammaLogicInput B)
  obtain ⟨hfinH,F,hF⟩ := gammaTracedSelectedHead_full_measured hκ hs hr hv T W hWG hW ρ hfin Q hLabels ω
  let E := gammaHeadSelectedNativeFullMeasuredBridge T ρ P Q hLabels hκ hs hr hv hTarget hfinH ω
  let H := F.comp hκ hs hr hv (E.symm hκ hs hr hv)
  refine ⟨H,?_⟩
  intro p
  let q := E.map.symm.map (F.map.map p)
  have hq := E.map.map.apply_inverse E.map.bijective (F.map.map p)
  have hE := gammaHeadSelectedNativeFullMeasuredBridge_value T ρ P Q hLabels hκ hs hr hv hTarget hfinH ω q
  exact (hE.symm.trans (congrArg Subtype.val hq)).trans (hF p)

end DiamondIntegral.Section3
