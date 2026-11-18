import «section 3».GammaNativeTypedMeasuredBridge
import «section 3».GammaSpecialPreparedFullComparison
import «section 3».GammaPreparedRVLabelMap

/-! Preparing a literal native lift gives an actual full measured VF
bijection with the precise retained-label Gamma form on its RV output. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (U : GammaObjectAt B Set.univ (n+1))
variable {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) l}
variable (T : SpecialBijection (typedLift U.object.obj) C) (hT : GammaChainDefinable B T.chain)
variable (hCP : IsRVPullback (carrier C))
variable (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))

def gammaNativePreparedFullMeasured : GammaFullMeasuredBijection
    (gammaNativeMeasuredLift U ω)
    (gammaNativeMeasuredLift (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T.chain hT) hCF)
      (ω.comp (gammaPreparedRVLabelMap U (normalizedTypedLift_presents U.object.obj) T hT hCF))) := by
  let A := gammaNativeTypedMeasuredData U ω
  let π := ω.comp (gammaPreparedRVLabelMap (hc := hc) U (normalizedTypedLift_presents U.object.obj) T hT hCF)
  have hπ : ∀ p, π (gammaNativePullbackKeyMap C (GammaChainDefinable.target B T.chain hT) hCF
      ((gammaNativeSpecialBijection T hT).map p)) = A.form p := by
    intro p
    change ω (gammaPreparedRVLabelMap U (normalizedTypedLift_presents U.object.obj) T hT hCF
      (gammaNativePullbackKeyMap C _ hCF ((gammaNativeSpecialBijection T hT).map p))) =
        ω (gammaNativeLiftLabel U ((gammaNativeTypedLiftBijection U).map p))
    congr 1
    apply Subtype.ext
    exact gammaPreparedRVLabelMap_at_source U (normalizedTypedLift_presents U.object.obj) T hT hCF p
  let F := gammaSpecialPreparedFullMeasured hκ hs hr hv T hT hCP hCF A.finite A.form π hπ
  let J := gammaNativeTypedFullMeasured hκ hs hr hv U ω
  exact (J.symm hκ hs hr hv).comp hκ hs hr hv F

theorem gammaNativePreparedFullMeasured_label
    (p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    gammaNativeLiftLabel (gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B T.chain hT) hCF)
      ((gammaNativePreparedFullMeasured hκ hs hr hv U T hT hCP hCF ω).map.map p) =
      gammaNativePullbackKeyMap C (GammaChainDefinable.target B T.chain hT) hCF
        ((gammaNativeSpecialBijection T hT).map ((gammaNativeTypedLiftBijection U).symm.map p)) := by
  exact gammaNativePullbackLiftBijection_label C _ hCP hCF
    ((gammaNativeSpecialBijection T hT).map ((gammaNativeTypedLiftBijection U).symm.map p))

end DiamondIntegral.Section3
