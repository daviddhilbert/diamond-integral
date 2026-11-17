import «section 3».GammaMeasuredElementaryObject
import «section 3».GammaLiftProductGeometry
import «section 5».Completed18LocalLift

/-! Conversion of native structural labels and elementary product charts
retains their literal values, rather than only their zero patterns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaNativeRVGroundVolume_value (U : GammaObjectAt B Set.univ n)
    (u : Section5.nativeRVGroundDomain (hc := hc) U) :
    (Section5.nativeRVGroundVolume U u).val =
      (rvObjectVolume U.object.obj (Section5.nativeRVGroundDomainEquiv U u)).val := by
  apply rvValues_injective
  change Section5.nativeRVRawVolume U (rvValues u.val) = _
  apply Section5.nativeRVRawVolume_eq
  exact (gammaRawObjectVolume_append_iff U.toGamma.toGammaRVObject _ _).mpr
    ⟨Section5.nativeRVGroundDomainEquiv U u,rfl,rfl⟩

theorem gammaBlowupValue_normalized (t : Fin n → CanonicalRV.RVSort M)
    (i : Fin n) (s : CanonicalRV.RVSort M) :
    @blowupValue M N hN n i t s = @blowupValue M sM hM n i t s := by
  unfold blowupValue
  funext j
  split_ifs
  · apply Subtype.ext
    rw [@RVOperations.mul_val M N hN,@RVOperations.mul_val M sM hM]
    exact CanonicalStructure.normalize_fun Fn.rvMul ![s.val,(t j).val]
      (fun k => by fin_cases k; exact s.property; exact (t j).property)
  · rfl

theorem gammaMeasuredElementaryChart_val
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundRVObject hc B (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U).toGamma.toGammaRVObject i)
    (w : Section5.nativeRVGroundDomain (hc := hc)
      (gammaHighRestrictionAt (gammaElementaryAt hκ hs h00 hr (Section5.groundRVAt U) i hAd))) :
    ((gammaMeasuredElementaryChart hκ hs h00 hr U i hAd).map w).val =
      (w.val ∘ Fin.castAdd 1,w.val ∘ Fin.natAdd U.arity) :=
  gammaRVUnpack_value U.domain (gammaGroundMeasuredRVPositive hc B).underlying.domain
    ((GammaGroundBijection.ofCarrierEq (gammaMeasuredElementary_positive_domain hκ hs h00 hr U i hAd)).map w)

end DiamondIntegral.Section3
