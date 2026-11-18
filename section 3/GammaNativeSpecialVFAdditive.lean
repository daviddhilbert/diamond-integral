import «section 3».GammaNativePreparedFullMeasure
import «section 3».GammaNativeFixedVFFullAdditive
import «section 3».GammaAdditiveSpecialComparison

/-! A full measured map following a Gamma special preparation preserves every additive elementary invariant. The remaining conjugate fixes the VF tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {W : Type*} [AddCommMonoid W]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (U : GammaObjectAt B Set.univ (n+1))
variable {K : DefSet (M := M) Set.univ (n+1) l}
variable (T : SpecialBijection (typedLift U.object.obj) K) (hT : GammaChainDefinable B T.chain)
variable (hKP : IsRVPullback (carrier K))
variable (hKF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject K)))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))

theorem gammaNativePreparedFullMeasured_additive_vf
    (p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    ((gammaNativePreparedFullMeasured hκ hs hr hv U T hT hKP hKF ω).map.map p).val.1 =
      (T.toMap ⟨((gammaNativeTypedLiftBijection U).symm.map p).val,
        ((gammaNativeTypedLiftBijection U).symm.map p).property⟩).val.1 := by
  let a := (gammaNativeTypedLiftBijection U).symm.map p
  change ((gammaNativePullbackLiftBijection K (GammaChainDefinable.target B T.chain hT) hKP hKF).map
    ((gammaNativeSpecialBijection T hT).map a)).val.1 = _
  exact (gammaNativePullbackLiftBijection_vf K (GammaChainDefinable.target B T.chain hT) hKP hKF
    ((gammaNativeSpecialBijection T hT).map a)).trans
      (congrArg Prod.fst (gammaNativeSpecialBijection_apply T hT a))

include hκ hs hr hv hT in
theorem gammaNativeSpecialVF_full_measured_additive_comparison
    (h00 : M ⊨ Axioms.ACVF00) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (V : GammaObjectAt B Set.univ (n+1))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (hVF : ∀ p, (f.map.map p).val.1 =
      (T.toMap ⟨((gammaNativeTypedLiftBijection U).symm.map p).val,
        ((gammaNativeTypedLiftBijection U).symm.map p).property⟩).val.1) :
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V η := by
  obtain ⟨hKF,hClass⟩ := gammaNativeAdditiveSpecial_comparison hκ hs h00 hr χ hχ U
    (normalizedTypedLift_presents U.object.obj) T hT ω
  have hKP' : IsRVPullback (carrier K) := T.preserves_pullback (typedLift_pullback U.object.obj)
  let F := gammaNativePreparedFullMeasured hκ hs hr hv U T hT hKP' hKF ω
  let P := gammaPullbackAt (Set.subset_univ _) K (GammaChainDefinable.target B T.chain hT) hKF
  let π := ω.comp (gammaPreparedRVLabelMap U (normalizedTypedLift_presents U.object.obj) T hT hKF)
  let g := (F.symm hκ hs hr hv).comp hκ hs hr hv f
  have hgVF : ∀ q, (g.map.map q).val.1 = q.val.1 := by
    intro q
    obtain ⟨p,rfl⟩ := F.map.bijective.surjective q
    have he : g.map.map (F.map.map p) = f.map.map p :=
      congrArg f.map.map (F.map.map.inverse_apply F.map.bijective p)
    exact (congrArg (fun q => q.val.1) he).trans
      ((hVF p).trans (gammaNativePreparedFullMeasured_additive_vf hκ hs hr hv U T hT hKP' hKF ω p).symm)
  exact hClass.trans (gammaNativeFixedVFFullMeasured_additive_comparison hκ hs h00 hr hg χ hχ hv C hBC P V π η g hgVF)

end DiamondIntegral.Section3
