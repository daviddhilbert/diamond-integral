import «section 3».GammaElementaryDensityEquation
import «section 3».GammaNativeUnitElementaryLift
import «section 5».Completed18RVIsomorphisms
import «section 3».GammaGroundRVFamilyObjects

/-! Native RV presentations carry arbitrary original-ground Gamma forms.
The label projection defines their VF forms without choosing RV values
for those densities. Elementary forms retain the original labels. -/
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
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaNativeLiftLabel (U : FiniteRV.GammaObjectAt B Set.univ n) :
    GammaGroundMap (gammaNativeUnitLift (hc := hc) U.toGamma).domain
      (Section5.nativeRVGroundDomain U) :=
  GammaGroundMap.ofGlobal _ _
    (universalProductSnd (SpecialTransformations.Section4.rawVFSpace n) (SpecialTransformations.Section4.rawRVSpace (rvObjectArity U.object.obj)) B.real)
    (fun p => by
      rw [Section5.nativeRVGroundDomain_carrier]
      obtain ⟨u,hu,_⟩ := p.property
      change p.val.2 ∈ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj))
      exact hu ▸ u.property)

@[simp] theorem gammaNativeLiftLabel_val (U : FiniteRV.GammaObjectAt B Set.univ n)
    (p : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    (gammaNativeLiftLabel U p).val = p.val.2 := rfl

def gammaNativeMeasuredLift (U : FiniteRV.GammaObjectAt B Set.univ n)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) :
    GammaGroundMeasuredVFData hc B n :=
  { gammaNativeUnitLift U.toGamma with form := ω.comp (gammaNativeLiftLabel U) }

def gammaNativeElementaryOldLabel
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : FiniteRV.GammaObjectAt B Set.univ n) (i : Fin n)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaGroundMap (Section5.nativeRVGroundDomain (FiniteRV.gammaElementaryAt hκ hs h00 hr U i hAd))
      (Section5.nativeRVGroundDomain (hc := hc) U) :=
  (gammaGroundRVSelectCoordinates (Fin.castAdd 1)
    (Section5.nativeRVGroundDomain (FiniteRV.gammaElementaryAt hκ hs h00 hr U i hAd))).corestrict (fun a => by
      rw [Section5.nativeRVGroundDomain_carrier]
      let a' : rvObjectDomain (FiniteRV.gammaElementaryAt hκ hs h00 hr U i hAd).object.obj :=
        ⟨a.val,(Section5.nativeRVGroundDomain_carrier _).le a.property⟩
      have hp := @elementaryProjection_labels M N hN Set.univ n U.object.obj i a'
      change (a.val ∘ Fin.castAdd 1) ∈ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj))
      exact Eq.mp (congrArg (fun t : Fin (rvObjectArity U.object.obj) → CanonicalRV.RVSort M =>
        t ∈ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj))) hp)
        (@elementaryProjection M N hN Set.univ n U.object.obj i a').property)

@[simp] theorem gammaNativeElementaryOldLabel_val
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : FiniteRV.GammaObjectAt B Set.univ n) (i : Fin n)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i)
    (a : Section5.nativeRVGroundDomain (hc := hc) (FiniteRV.gammaElementaryAt hκ hs h00 hr U i hAd)) :
    (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd a).val = a.val ∘ Fin.castAdd 1 := rfl

end DiamondIntegral.Section3
