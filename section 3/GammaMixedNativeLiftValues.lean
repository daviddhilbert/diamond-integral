import «section 3».GammaNativeLiftFullKeyValues
import «section 3».GammaMixedContractionValues

/-! Contracting an actual native measured lift recovers the original
normalized RV class. This is proved using the literal full key and
arbitrary-order comparison, independently of the reverse kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMixed_native_lift_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    gammaMixedContractionValue C hBC hv hNames hGenerated (gammaNativeMeasuredLift U ω) =
      gammaMeasuredPrincipalValue (gammaNativeMeasuredNormalization U ω) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let P := gammaRetainedNativeLiftData U ω
  let E : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) P.toMeasured :=
    gammaFullMeasuredFixedVF C.uncountable.le C.saturated hr hv
      (GammaGroundBijection.ofCarrierEq rfl) (fun _ => rfl) (fun _ => rfl)
  have hP := gammaMixed_contraction_value_of_presentation C hBC hv hNames hGenerated hg δ hδ hδ1
    (gammaNativeMeasuredLift U ω) P E (fun _ => rfl)
  let A := P.nativeSet C hNames
  have hPull : IsRVPullback (carrier A) := gammaNativeLift_isRVPullback (hc := hc) U
  let hAF := pullbackObject_finiteVolume A hPull P.finite
  obtain ⟨T,hT,hVal⟩ := gammaCanonical_pullback_measured_value_exists C hBC A P.point_definable hAF
    ω.extendByOne P.finite hPull
  exact hP.trans ((P.contractionValue_eq C hBC hNames hGenerated hv hg δ hδ hδ1 T hT).trans
    (hVal.trans (gammaNativeLift_full_key_value C hBC hNames U ω hAF)))

end DiamondIntegral.Section3
