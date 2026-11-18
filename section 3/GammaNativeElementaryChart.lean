import «section 3».GammaNativeElementaryDomain
import «section 3».GammaNativeStructuralValues

/-! The actual elementary product chart on native original-ground
objects preserves its full structural volume formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
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
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)

def gammaNativeElementaryChart (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaGroundBijection (Section5.nativeRVGroundDomain (gammaHighRestrictionAt
      (gammaElementaryAt hκ hs h00 hr U i hAd)))
      ((Section5.nativeRVGroundDomain (hc := hc) U).prod (gammaGroundMeasuredRVPositive hc B).underlying.domain) :=
  (gammaGroundRVPackBijection (Section5.nativeRVGroundDomain U)
    (gammaGroundMeasuredRVPositive hc B).underlying.domain).symm.comp
      (GammaGroundBijection.ofCarrierEq (gammaNativeElementary_positive_domain hκ hs h00 hr U hfull i hAd))

theorem gammaNativeElementaryChart_val (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (gammaElementaryAt hκ hs h00 hr U i hAd))) :
    ((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).val =
      (w.val ∘ Fin.castAdd 1,w.val ∘ Fin.natAdd (rvObjectArity U.object.obj)) :=
  gammaRVUnpack_value (Section5.nativeRVGroundDomain U) (gammaGroundMeasuredRVPositive hc B).underlying.domain
    ((GammaGroundBijection.ofCarrierEq (gammaNativeElementary_positive_domain hκ hs h00 hr U hfull i hAd)).map w)

theorem gammaNativeElementaryChart_volume (U : GammaObjectAt B Set.univ (n+1)) (hfull : GammaFullWeightAt U)
    (i : Fin (n+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (w : Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (gammaElementaryAt hκ hs h00 hr U i hAd))) :
    (Section5.nativeRVGroundVolume (gammaHighRestrictionAt (gammaElementaryAt hκ hs h00 hr U i hAd)) w).val =
      blowupValue i (Section5.nativeRVGroundVolume U
        ⟨((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).val.1,
          ((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).property.1⟩).val
        ((show Fin 1 → CanonicalRV.RVSort M from ((gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w).val.2) 0) := by
  let E := gammaElementaryAt hκ hs h00 hr U i hAd
  let H := gammaHighRestrictionAt E
  let a : rvObjectDomain E.object.obj := ⟨w.val,((Section5.nativeRVGroundDomain_carrier H).le w.property).1⟩
  let u := @elementaryProjection M N hN Set.univ (n+1) U.object.obj i a
  let s := @elementaryParameter M N hN Set.univ (n+1) U.object.obj i a
  let z := (gammaNativeElementaryChart hκ hs h00 hr U hfull i hAd).map w
  have hZ := gammaNativeElementaryChart_val hκ hs h00 hr U hfull i hAd w
  have hu : Section5.nativeRVGroundDomainEquiv U ⟨z.val.1,z.property.1⟩ = u := by
    apply Subtype.ext
    exact (congrArg Prod.fst hZ).trans
      (@elementaryProjection_labels M N hN Set.univ (n+1) U.object.obj i a).symm
  have hsZ : s.val = z.val.2 :=
    (@elementaryParameter_labels M N hN Set.univ (n+1) U.object.obj i a).trans
      (congrArg Prod.snd hZ).symm
  have hV : (Section5.nativeRVGroundVolume H w).val = @RVObject.value M N Set.univ (n+1) E.object.obj a :=
    gammaNativeRVGroundVolume_value H w
  rw [hV]
  change @blowupValue M N hN (n+1) i (@RVObject.value M N Set.univ (n+1) U.object.obj u) (s.val 0) = _
  have hvol : @RVObject.value M N Set.univ (n+1) U.object.obj u =
      (Section5.nativeRVGroundVolume U ⟨z.val.1,z.property.1⟩).val := by
    rw [gammaNativeRVGroundVolume_value,hu]
    rfl
  exact (@gammaBlowupValue_normalized M sM hM (n+1)
    (@RVObject.value M N Set.univ (n+1) U.object.obj u) i (s.val 0)).trans
      (congrArg₂ (@blowupValue M sM hM (n+1) i) hvol (congrFun hsZ 0))

end DiamondIntegral.Section3
