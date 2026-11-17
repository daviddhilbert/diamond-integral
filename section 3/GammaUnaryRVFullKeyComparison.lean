import «section 3».GammaNativePreparedFullMeasure
import IntegrationSection5.UnaryRVCategory
import IntegrationSection5.UnaryConjugationGeometry

/-! The actual RV isomorphism produced by unary preparation acts on the
literal native full keys, including every retained source label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r s : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaUnaryRV_full_key_comparison (U V : GammaObjectAt B Set.univ 1)
    {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ 1 r}
    {D : SpecialTransformations.Section5.DefSet (M := M) Set.univ 1 s}
    (TU : SpecialBijection (typedLift U.object.obj) C) (TV : SpecialBijection (typedLift V.object.obj) D)
    (hTU : GammaChainDefinable B TU.chain) (hTV : GammaChainDefinable B TV.chain)
    (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (f : Map (typedLift U.object.obj) (typedLift V.object.obj))
    (e : @CategoryTheory.Iso (@SpecialTransformations.Section4.RVObject M N Set.univ 1) _ (pullbackObject C) (pullbackObject D))
    (he : ∀ c : C, IntegrationInACVF.Section5.unaryIsoHomMap e (Map.toImage (rawKeyMap C) c) =
      Map.toImage (rawKeyMap D) (IntegrationInACVF.Section5.unaryConjugate TU TV f c))
    (heΓ : GammaGraphDefinable B (IntegrationInACVF.Section5.rvPullbackMapGraph (IntegrationInACVF.Section5.unaryIsoHomMap e))) :
    let PC := gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B TU.chain hTU) hCF
    let PD := gammaPullbackAt (Set.subset_univ _) D (GammaChainDefinable.target B TV.chain hTV) hDF
    let E : GammaIsoAt PC PD := GammaIsoAt.ofAmbient e heΓ
    ∀ a : Section5.nativeGammaPointDomain (hc := hc) (carrier (typedLift U.object.obj)) (gammaNativeTypedLift_definable U),
      (Section5.nativeRVGroundIso E).map
        (gammaNativePullbackKeyMap C (GammaChainDefinable.target B TU.chain hTU) hCF ((gammaNativeSpecialBijection TU hTU).map a)) =
      gammaNativePullbackKeyMap D (GammaChainDefinable.target B TV.chain hTV) hDF
        ((gammaNativeSpecialBijection TV hTV).map (f a)) := by
  intro PC PD E a
  let b : typedLift U.object.obj := ⟨a.val,a.property⟩
  let c := TU.toMap b
  let u := Section5.nativeRVGroundDomainEquiv PC
    (gammaNativePullbackKeyMap C (GammaChainDefinable.target B TU.chain hTU) hCF ((gammaNativeSpecialBijection TU hTU).map a))
  have hu : u = Map.toImage (rawKeyMap C) c := by
    apply Subtype.ext
    change Fin.append (Section2.tupleRV M ((gammaNativeSpecialBijection TU hTU).map a).val.1)
      ((gammaNativeSpecialBijection TU hTU).map a).val.2 = _
    rw [gammaNativeSpecialBijection_apply]
    rfl
  have hg : IntegrationInACVF.Section5.unaryConjugate TU TV f c = TV.toMap (f b) := by
    change TV.toMap (f (TU.inverseMap (TU.toMap b))) = _
    rw [TU.inverse_apply]
  apply Subtype.ext
  change ((IntegrationInACVF.Section5.unaryIsoHomMap e) u).val =
    Fin.append (Section2.tupleRV M ((gammaNativeSpecialBijection TV hTV).map (f a)).val.1)
      ((gammaNativeSpecialBijection TV hTV).map (f a)).val.2
  rw [hu,gammaNativeSpecialBijection_apply]
  have H := (he c).trans (congrArg (Map.toImage (rawKeyMap D)) hg)
  exact congrArg (fun z : rvObjectDomain (pullbackObject D) => z.val) H

end DiamondIntegral.Section3
