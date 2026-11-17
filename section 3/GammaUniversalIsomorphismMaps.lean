import «section 3».GammaNativeStructuralValues
import IntegrationSection6.FiniteGammaUniversalCharts

/-! Universal real presentation of an inherited Gamma RV isomorphism,
exposing its original label map for density compatibility checks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaUniversalIsoAt (U V : GammaRVFiniteObject B k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    GammaIsoAt (gammaUniversalObject U) (gammaUniversalObject V) := by
  let A := gammaUniversalObject U
  let D := gammaUniversalObject V
  let F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ Set.univ
      (rvObjectDomain A.object.obj) (rvObjectDomain D.object.obj) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ _ _ _ e.equiv (by
      obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize e.graph
      exact @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
        (@rawRVSpace M N (rvObjectArity U.object)) (@rawRVSpace M N (rvObjectArity V.object))
        (B.real ∪ Set.range (rawTuple t)) Set.univ _ hr (Set.subset_univ _))
  have hw (u : rvObjectDomain A.object.obj) :
      @rvWeight M N k (@SpecialTransformations.Section4.RVObject.value M N Set.univ k A.object.obj u) =
      @rvWeight M N k (@SpecialTransformations.Section4.RVObject.value M N Set.univ k D.object.obj (F u)) :=
    (rawWeight_eq_normalized_weight (gammaVolumeValue U.toGammaRVObject u)).symm.trans
      ((e.weight u).trans (rawWeight_eq_normalized_weight (gammaVolumeValue V.toGammaRVObject (e.equiv u))))
  exact ⟨@isoOfDefinableBijection M N Set.univ k A.object D.object F e.equiv.bijective hw,e.graph⟩

theorem gammaUniversalIsoAt_map (U V : GammaRVFiniteObject B k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject U)) :
    ((Section5.nativeRVGroundIso (gammaUniversalIsoAt U V e)).map u).val =
      (e.equiv (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject U) u)).val := rfl

end DiamondIntegral.Section3
