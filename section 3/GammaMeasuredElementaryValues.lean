import «section 3».GammaNativeStructuralValues
import «section 3».GammaElementaryRadiusProduct

/-! The weighted elementary presentation retains the actual structural
volume formula on its nonzero domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
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
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaMeasuredElementaryObject_volume
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundMeasuredRVObject hc B (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible (Section5.groundRVAt U.underlying).toGamma.toGammaRVObject i)
    (w : (gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.domain) :
    ((gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.volume w).val =
      blowupValue i
        (U.underlying.volume ⟨((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.1,
          ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).property.1⟩).val
        ((show Fin 1 → CanonicalRV.RVSort M from ((gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w).val.2) 0) := by
  let A := Section5.groundRVAt U.underlying
  let E := gammaElementaryAt hκ hs h00 hr A i hAd
  let H := gammaHighRestrictionAt E
  let a : rvObjectDomain E.object.obj :=
    ⟨w.val,((Section5.nativeRVGroundDomain_carrier H).le w.property).1⟩
  let u := @elementaryProjection M N hN Set.univ (n+1) A.object.obj i a
  let s := @elementaryParameter M N hN Set.univ (n+1) A.object.obj i a
  let z := (gammaMeasuredElementaryChart hκ hs h00 hr U.underlying i hAd).map w
  have hZ := gammaMeasuredElementaryChart_val hκ hs h00 hr U.underlying i hAd w
  have hu : (Section5.groundRVAtDomainEquiv U.underlying).symm u = ⟨z.val.1,z.property.1⟩ := by
    apply Subtype.ext
    exact (@elementaryProjection_labels M N hN Set.univ (n+1) A.object.obj i a).trans
      (congrArg Prod.fst hZ).symm
  have hsZ : s.val = z.val.2 :=
    (@elementaryParameter_labels M N hN Set.univ (n+1) A.object.obj i a).trans
      (congrArg Prod.snd hZ).symm
  have hV : ((gammaMeasuredElementaryObject hκ hs h00 hr U i hAd).underlying.volume w).val =
      @RVObject.value M N Set.univ (n+1) E.object.obj a :=
    gammaNativeRVGroundVolume_value H w
  rw [hV]
  change @blowupValue M N hN (n+1) i (@RVObject.value M N Set.univ (n+1) A.object.obj u) (s.val 0) = _
  have hvol : @RVObject.value M N Set.univ (n+1) A.object.obj u =
      (U.underlying.volume ⟨z.val.1,z.property.1⟩).val :=
    (Section5.groundRVAt_volume_eq U.underlying u).trans
      (congrArg (fun q : U.underlying.domain => (U.underlying.volume q).val) hu)
  exact (@gammaBlowupValue_normalized M sM hM (n+1)
    (@RVObject.value M N Set.univ (n+1) A.object.obj u) i (s.val 0)).trans
      (congrArg₂ (@blowupValue M sM hM (n+1) i) hvol (congrFun hsZ 0))

end DiamondIntegral.Section3
