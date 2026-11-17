import «section 3».GammaNativeFiniteCodeExtensions
import Integration7.CanonicalContractionKeySquares

/-! Canonical pullback contraction and raw-volume normalization preserve
arbitrary retained Gamma forms. Both use the existing actual Gamma RV
isomorphisms with their full coordinate and every-old-label identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
variable (hA : GammaSetDefinable B (carrier A))
variable (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
variable {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
variable (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))

def gammaCanonical_measured_contraction
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (hVF : ∀ p : A, (T.naturalMap p).val.1 = p.val.1) (hcon : Contractible T.toMap) :
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let U := gammaNativeFiniteAt (gammaPullbackAt hBC A hA hAF).toGamma
    let V := gammaNativeFiniteAt (gammaFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT)
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization U (gammaNativeTotalRVForm U (Fin.natAdd (n+1)) ω))
      (gammaNativeMeasuredNormalization V (gammaNativeTotalRVForm V (contractionOldLabelIndex T) ω)) := by
  intro hr U V
  let e := gammaCanonicalContractionIso C.uncountable.le C.saturated hr hBC hA hfin hAF T hT hVF hcon
  apply gammaNativeRetainedRVHom (GammaGroundDefSet.univ hc B (rawRVSpace a))
    (Fin.natAdd (n+1)) (contractionOldLabelIndex T)
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) ω (gammaNativeFiniteIso e)
  · intro u
    exact congrArg (fun t : Fin (n+1) → RV (M := M) => ∏ i, Values.vrv (t i))
      (canonical_contraction_coordinates C.uncountable.le C.saturated hr hBC hA hfin hAF T hT hVF hcon u)
  · intro u
    funext i
    exact canonical_contraction_retained_labels C.uncountable.le C.saturated hr hBC hA hfin hAF T hT hVF hcon u i

def gammaRaw_normalization_measured_contraction :
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let U := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT)
    let V := gammaNativeFiniteAt (gammaFiniteContraction C.uncountable.le C.saturated hr hBC hA hfin T hT)
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization U (gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω))
      (gammaNativeMeasuredNormalization V (gammaNativeTotalRVForm V (contractionOldLabelIndex T) ω)) := by
  intro hr U V
  let e := gammaRawFiniteNormalizationIso C.uncountable.le C.saturated hr hBC hA hfin T hT
  apply gammaNativeRetainedRVHom (GammaGroundDefSet.univ hc B (rawRVSpace a))
    (suffixIndex T.program.rvArity_le) (contractionOldLabelIndex T)
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) ω (gammaNativeFiniteIso e)
  · intro u
    exact congrArg (fun t : Fin (n+1) → RV (M := M) => ∏ i, Values.vrv (t i))
      (toFirstVolume_volume (SpecialTransformations.Section5.Map.image (rawLabelMap T.target)) T.volumeIndex u)
  · intro u
    funext i
    exact toFirstVolume_oldLabels _ _ u (suffixIndex T.program.rvArity_le i)

end DiamondIntegral.Section3
