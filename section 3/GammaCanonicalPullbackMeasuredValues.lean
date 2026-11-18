import «section 3».GammaCanonicalMeasuredContractions
import «section 3».GammaNativeEndpointRawClasses
import IntegrationSection6.CanonicalContractionPrograms

/-! A canonical contraction of a pullback has precisely its full-key
Gamma measured class. Both comparisons use actual normalized RV maps,
with the complete structural volume and original retained density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M)) {n a : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
variable (hA : GammaSetDefinable B (carrier A))
variable (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
variable (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))

def gammaNativePullbackTotalMeasuredObject : GammaGroundMeasuredRVObject hc B (n+1) :=
  let U := gammaNativeFiniteAt (gammaPullbackAt hBC A hA hAF).toGamma
  gammaNativeMeasuredNormalization U (gammaNativeTotalRVForm U (Fin.natAdd (n+1)) ω)

theorem gammaCanonical_pullback_measured_value
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (hVF : ∀ p : A, (T.naturalMap p).val.1 = p.val.1) (hcon : Contractible T.toMap) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativePullbackTotalMeasuredObject C hBC A hA hAF ω) := by
  have hRaw := gammaMeasuredPrincipalValue_iso (gammaRaw_normalization_measured_contraction C hBC A hA hfin T hT ω)
  have hCanonical := gammaMeasuredPrincipalValue_iso (gammaCanonical_measured_contraction C hBC A hA hfin T hT ω hAF hVF hcon)
  exact hRaw.trans hCanonical.symm

theorem gammaCanonical_pullback_measured_value_exists
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hPull : IsRVPullback (carrier A)) :
    ∃ T : StandardContraction A (Equiv.refl _), ∃ hT : GammaProgramDefinable B T.program,
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) =
        gammaMeasuredPrincipalValue (gammaNativePullbackTotalMeasuredObject C hBC A hA hAF ω) := by
  obtain ⟨T,hT,hVF,hcon⟩ := canonical_standard_contraction_exists A hA hPull
  exact ⟨T,hT,gammaCanonical_pullback_measured_value C hBC A hA hAF ω hfin T hT hVF hcon⟩

end DiamondIntegral.Section3
