import «section 3».GammaMeasuredNativeRoundTrips
import «section 3».GammaNativeElementaryCongruence

/-! Native elementary steps are actual local measured elementary steps,
up to measured isomorphism. The comparison reuses both checked product
charts and their exact combined-weight formulas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

theorem gammaNativeGround_admissible
    (U : GammaObjectAt B Set.univ (k+1)) (hU : GammaFullWeightAt U) (i : Fin (k+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    GammaAdmissible (Section5.groundRVAt (Section5.nativeRVGroundObject (hc := hc) U hU)).toGamma.toGammaRVObject i := by
  let P := Section5.nativeRVGroundObject (hc := hc) U hU
  let A := Section5.groundRVAt P
  let f (u : rvObjectDomain A.object.obj) := Section5.nativeRVGroundDomainEquiv (hc := hc) U
    ((Section5.groundRVAtDomainEquiv P).symm u)
  have hVolume (u : rvObjectDomain A.object.obj) :
      gammaVolumeValue A.toGamma.toGammaRVObject u = gammaVolumeValue U.toGamma.toGammaRVObject (f u) := by
    have h := (Section5.groundRVAt_volume_eq P u).trans
      (gammaNativeRVGroundVolume_value U ((Section5.groundRVAtDomainEquiv P).symm u))
    exact h
  constructor
  · intro u
    rw [hVolume u]
    exact hAd.nonzero (f u)
  · intro u
    rw [hVolume u]
    exact hAd.algebraic (f u)

theorem gammaNativeElementary_local_measured_hom
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (k+1)) (hU : GammaFullWeightAt U)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (i : Fin (k+1)) (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    let P : GammaGroundMeasuredRVObject hc B (k+1) := ⟨Section5.nativeRVGroundObject U hU,ω⟩
    Nonempty (GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr U i hAd)
        (ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr U i hAd)))
      (gammaMeasuredElementaryObject hκ hs h00 hr P i (gammaNativeGround_admissible U hU i hAd))) := by
  intro P
  let hAP := gammaNativeGround_admissible (hc := hc) U hU i hAd
  let CN := gammaNativeElementaryChart (hc := hc) hκ hs h00 hr U hU i hAd
  let CL := gammaMeasuredElementaryChart hκ hs h00 hr P.underlying i hAP
  let f := CL.symm.comp CN
  refine ⟨⟨f,fun w => ?_⟩⟩
  have hN := gammaNativeElementary_weight hκ hs h00 hr U hU ω i hAd w
  have hL := gammaMeasuredElementaryObject_weight hκ hs h00 hr P i hAP (f.map w)
  have hSquare : CL.map (f.map w) = CN.map w := CL.map.apply_inverse CL.bijective _
  change _ = P.combinedWeight ⟨(CL.map (f.map w)).val.1,(CL.map (f.map w)).property.1⟩ *
    (gammaGroundMeasuredRVPositive hc B).combinedWeight
      ⟨(CL.map (f.map w)).val.2,(CL.map (f.map w)).property.2⟩ at hL
  rw [hSquare] at hL
  exact hN.trans hL.symm

end DiamondIntegral.Section3
