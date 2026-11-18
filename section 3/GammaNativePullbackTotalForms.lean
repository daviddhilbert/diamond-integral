import «section 3».GammaCanonicalPullbackMeasuredValues
import «section 3».GammaNativeRetainedFullMaps
import «section 3».GammaMatchingPreparedMeasuredComparison

/-! Surjective full keys identify the descended retained Gamma form
with its literal coordinate pullback. This relates the prepared matching
objects to the same canonical pullback class used by contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}

theorem gammaNativePullback_total_form
    (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    let Ω := gammaPointRetainedForm A hA (GammaGroundDefSet.univ hc B (rawRVSpace a)) id
      (fun _ => Set.mem_univ _) ω
    let hΩ : ∀ p q : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA,
      p.val.2 = q.val.2 → Ω p = Ω q := fun _ _ he => congrArg ω (Subtype.ext he)
    gammaNativePullbackForm A hA hAF Ω hΩ =
      gammaNativeTotalRVForm (gammaPullbackAt (Set.subset_univ _) A hA hAF) (Fin.natAdd (n+1)) ω := by
  intro Ω hΩ
  apply GammaGroundMap.ext
  intro u
  obtain ⟨p,rfl⟩ := gammaNativePullbackKeyMap_surjective A hA hAF u
  rw [gammaNativePullbackForm_apply]
  apply congrArg ω
  apply Subtype.ext
  funext i
  exact (Fin.append_right (Section2.tupleRV M p.val.1) p.val.2 i).symm

theorem gammaPreparedRectangle_total_object
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {m : ℕ} {H V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    (P : RectangleFamilyPullbackPreparation B V)
    (v : SpecialTransformations.Section5.Map H V) (hv : Function.Bijective v)
    (hvΓ : GammaGraphDefinable B (pointMapGraph v))
    (hvLabels : ∀ p : H, (v p).val.2 = p.val.2)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m))) :
    let hAF := P.finite_volume C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) v hv hvΓ hfin
    gammaPreparedRectangleRVObject C hBC P v hv hvΓ hvLabels hfin
      (GammaGroundDefSet.univ hc B (rawRVSpace m)) (fun _ => Set.mem_univ _) ω =
      gammaNativePullbackTotalMeasuredObject C hBC P.volumeTarget P.volume_target_gamma hAF
        (gammaTotalRVCoordinateForm P.volumeLabelIndex ω) := by
  intro hAF
  let A := extendBase P.volumeTarget (Set.subset_univ _)
  let η := gammaTotalRVCoordinateForm P.volumeLabelIndex ω
  change gammaNativeMeasuredNormalization
      (gammaPullbackAt (Set.subset_univ _) A P.volume_target_gamma hAF)
      (gammaNativePullbackForm A P.volume_target_gamma hAF
        (gammaPreparedRectangle_retained_form P v hv hvLabels
          (GammaGroundDefSet.univ hc B (rawRVSpace m)) (fun _ => Set.mem_univ _) ω) _) =
    gammaNativeMeasuredNormalization
      (gammaPullbackAt (Set.subset_univ _) A P.volume_target_gamma hAF)
      (gammaNativeTotalRVForm (gammaPullbackAt (Set.subset_univ _) A P.volume_target_gamma hAF)
        (Fin.natAdd 2) η)
  apply congrArg (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) A P.volume_target_gamma hAF))
  apply GammaGroundMap.ext
  intro u
  obtain ⟨p,rfl⟩ := gammaNativePullbackKeyMap_surjective A P.volume_target_gamma hAF u
  rw [gammaNativePullbackForm_apply]
  apply congrArg ω
  apply Subtype.ext
  funext i
  exact (Fin.append_right (Section2.tupleRV M p.val.1) p.val.2 (P.volumeLabelIndex i)).symm

end DiamondIntegral.Section3
