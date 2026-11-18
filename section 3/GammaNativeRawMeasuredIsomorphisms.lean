import «section 3».GammaNativeMeasuredIsomorphisms
import «section 5».Completed18RVGraphs
import IntegrationSection6.GammaRVSetRealization

/-! Actual original-Gamma RV isomorphisms with structural-volume and
Gamma-form identities give measured normalized arrows. This accepts
the existing rectangle and canonical-contraction geometric exports. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaIsoAtOfGamma {U V : GammaObjectAt B Set.univ n}
    (e : GammaRVIso U.toGamma.toGammaRVObject V.toGamma.toGammaRVObject) : GammaIsoAt U V := by
  let f : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ Set.univ
      (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) := by
    refine @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ Set.univ
      (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) e.equiv ?_
    obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize e.graph
    exact @Space.RelationDefinable.mono LRV M N _ _ _ Set.univ _ hr (Set.subset_univ _)
  refine ⟨@isoOfDefinableBijection M N Set.univ n U.object V.object f e.equiv.bijective ?_,e.graph⟩
  intro u
  have h := e.weight u
  have hU := rawWeight_eq_normalized_weight (gammaVolumeValue U.toGamma.toGammaRVObject u)
  have hV := rawWeight_eq_normalized_weight (gammaVolumeValue V.toGamma.toGammaRVObject (e.equiv u))
  rw [hU,hV] at h
  exact h

def gammaNativeRawMeasuredHom
    {U V : GammaObjectAt B Set.univ (n+1)}
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (e : GammaRVIso U.toGamma.toGammaRVObject V.toGamma.toGammaRVObject)
    (hVolume : ∀ u : Section5.nativeRVGroundDomain (hc := hc) U, ∏ i, Values.vrv ((Section5.nativeRVGroundVolume (hc := hc) V
        ((Section5.nativeRVGroundIso (hc := hc) (gammaIsoAtOfGamma e)).map u)).val i) =
      ∏ i, Values.vrv ((Section5.nativeRVGroundVolume (hc := hc) U u).val i))
    (hForm : ∀ u : Section5.nativeRVGroundDomain (hc := hc) U, η ((Section5.nativeRVGroundIso (hc := hc) (gammaIsoAtOfGamma e)).map u) = ω u) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  apply gammaNativeMeasuredNormalizationHom ω η (gammaIsoAtOfGamma e)
  intro u
  unfold gammaNativeCombinedWeight
  rw [hVolume]
  exact congrArg (fun q => (cast (gammaCarrier hc) q.val).val *
    ∏ i, Values.vrv ((Section5.nativeRVGroundVolume (hc := hc) U u).val i)) (hForm u).symm

end DiamondIntegral.Section3
