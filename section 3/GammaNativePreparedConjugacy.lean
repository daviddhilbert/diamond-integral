import «section 3».GammaNativePreparedFullMeasure
import «section 3».GammaNativeTypedConjugacy
import «section 3».GammaNativeFullLabelMeasuredDescent

/-! Compatible full-key unary preparation retains the actual Gamma
measure identity under conjugacy and descends it to the terminal RV map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (U V : GammaObjectAt B Set.univ (n+1))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
variable (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
variable (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
variable {C : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) r}
variable {D : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) s}
variable (TU : SpecialBijection (typedLift U.object.obj) C) (TV : SpecialBijection (typedLift V.object.obj) D)
variable (hTU : GammaChainDefinable B TU.chain) (hTV : GammaChainDefinable B TV.chain)
variable (hCP : IsRVPullback (carrier C)) (hDP : IsRVPullback (carrier D))
variable (hCF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject C)))
variable (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
local notation "PC" => gammaPullbackAt (Set.subset_univ _) C (GammaChainDefinable.target B TU.chain hTU) hCF
local notation "PD" => gammaPullbackAt (Set.subset_univ _) D (GammaChainDefinable.target B TV.chain hTV) hDF
local notation "ωC" => ω.comp (gammaPreparedRVLabelMap U (normalizedTypedLift_presents U.object.obj) TU hTU hCF)
local notation "ηD" => η.comp (gammaPreparedRVLabelMap V (normalizedTypedLift_presents V.object.obj) TV hTV hDF)

def gammaNativePreparedFullConjugate : GammaFullMeasuredBijection
    (gammaNativeMeasuredLift PC ωC) (gammaNativeMeasuredLift PD ηD) :=
  (((gammaNativePreparedFullMeasured hκ hs hr hv U TU hTU hCP hCF ω).symm hκ hs hr hv).comp hκ hs hr hv f).comp hκ hs hr hv
    (gammaNativePreparedFullMeasured hκ hs hr hv V TV hTV hDP hDF η)

theorem gammaNativePreparedConjugate_label (e : GammaIsoAt PC PD)
    (hSpec : ∀ a : Section5.nativeGammaPointDomain (hc := hc) (carrier (typedLift U.object.obj)) (gammaNativeTypedLift_definable U),
      (Section5.nativeRVGroundIso e).map
        (gammaNativePullbackKeyMap C (GammaChainDefinable.target B TU.chain hTU) hCF ((gammaNativeSpecialBijection TU hTU).map a)) =
      gammaNativePullbackKeyMap D (GammaChainDefinable.target B TV.chain hTV) hDF
        ((gammaNativeSpecialBijection TV hTV).map (gammaNativeTypedMeasuredMap hκ hs hr hv U V ω η f a)))
    (p : (gammaNativeUnitLift (hc := hc) (PC).toGamma).domain) :
    gammaNativeLiftLabel PD
      ((gammaNativePreparedFullConjugate hκ hs hr hv U V ω η f TU TV hTU hTV hCP hDP hCF hDF).map.map p) =
      (Section5.nativeRVGroundIso e).map (gammaNativeLiftLabel PC p) := by
  let FU := gammaNativePreparedFullMeasured hκ hs hr hv U TU hTU hCP hCF ω
  let FV := gammaNativePreparedFullMeasured hκ hs hr hv V TV hTV hDP hDF η
  obtain ⟨a,ha⟩ := FU.map.bijective.2 p
  have he : (gammaNativePreparedFullConjugate hκ hs hr hv U V ω η f TU TV hTU hTV hCP hDP hCF hDF).map.map (FU.map.map a) =
      FV.map.map (f.map.map a) := by
    exact congrArg (fun q => FV.map.map (f.map.map q)) (FU.map.map.inverse_apply FU.map.bijective a)
  rw [← ha,he,gammaNativePreparedFullMeasured_label,gammaNativePreparedFullMeasured_label]
  have H := hSpec ((gammaNativeTypedLiftBijection U).symm.map a)
  rw [gammaNativeTypedMeasuredMap_source_inverse] at H
  exact H.symm

end DiamondIntegral.Section3
