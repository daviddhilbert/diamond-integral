import «section 3».GammaMeasuredGeometricRelations
import «section 3».GammaMeasuredNativeRoundTrips
import «section 3».GammaNativeElementaryCongruence
import «section 3».GammaMeasuredPointFocus
import «section 3».GammaGroundMeasuredRVProductMorphisms

/-! The stated point/cone generator, multiplied by any measured
coefficient object, has a finite native elementary derivation in its
actual homogeneous degree. No cancellation is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaMeasuredPointProductProjection (U : GammaGroundMeasuredRVObject hc B n) :
    GammaGroundBijection (U.product (gammaMeasuredPointZeroArity hc B)).underlying.domain U.underlying.domain :=
  gammaGroundRVProductRightUnitBijection U.underlying

theorem gammaMeasuredPointProduct_weight (U : GammaGroundMeasuredRVObject hc B n)
    (u : (U.product (gammaMeasuredPointZeroArity hc B)).underlying.domain) :
    (U.product (gammaMeasuredPointZeroArity hc B)).combinedWeight u =
      U.combinedWeight ((gammaMeasuredPointProductProjection U).map u) := by
  rw [GammaGroundMeasuredRVObject.product_combined,gammaMeasuredPointZeroArity_weight,mul_one]
  rfl

theorem gammaMeasuredPointProduct_admissible (U : GammaGroundMeasuredRVObject hc B n) :
    GammaAdmissible (Section5.groundRVAt (U.product (gammaMeasuredPointZeroArity hc B)).underlying).toGamma.toGammaRVObject (Fin.last n) := by
  let W := U.product (gammaMeasuredPointZeroArity hc B)
  let A := Section5.groundRVAt W.underlying
  have hLast (u : rvObjectDomain A.object.obj) :
      (gammaVolumeValue A.toGamma.toGammaRVObject u (Fin.last n)).val = iRVOne := by
    have h := congrArg (fun t : Fin (n+1) → CanonicalRV.RVSort M => (t (Fin.last n)).val)
      (Section5.groundRVAt_volume_eq W.underlying u)
    have hRight : ((W.underlying.volume ((Section5.groundRVAtDomainEquiv W.underlying).symm u)).val (Fin.last n)).val = iRVOne := by
      let w := (Section5.groundRVAtDomainEquiv W.underlying).symm u
      let ab := gammaGroundRVUnpack U.underlying.domain (gammaMeasuredPointZeroArity hc B).underlying.domain w
      change (Fin.append (U.underlying.volume ⟨ab.val.1,ab.property.1⟩).val
        ((gammaMeasuredPointZeroArity hc B).underlying.volume ⟨ab.val.2,ab.property.2⟩).val
        (Fin.natAdd n (0 : Fin 1))).val = iRVOne
      rw [Fin.append_right]
      rfl
    exact h.trans hRight
  constructor
  · intro u hu
    exact RVCalc.rv_one_ne_zero (inferInstance : M ⊨ Axioms.ACVF) ((hLast u).symm.trans hu)
  · intro u
    exact (hLast u).symm ▸ gamma_rv_one_algebraic _

theorem gammaPoint_cone_product_geometric
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaGroundMeasuredRVObject hc B n) :
    GammaMeasuredGeometricRelation hκ hs h00 hr
      (U.product (gammaGroundMeasuredRVOne hc B)) (U.product (gammaGroundMeasuredRVPositive hc B)) := by
  let W := U.product (gammaMeasuredPointZeroArity hc B)
  let A := Section5.groundRVAt W.underlying
  let hFull := Section5.groundRVAt_full W.underlying
  let Ω := gammaGroundMeasuredNativeForm W
  let hAd := gammaMeasuredPointProduct_admissible U
  let RT := gammaGroundMeasuredNativeRoundTrip W
  let NR := gammaNativeFullWeightNormalizationHom A hFull Ω
  let sourceIso := RT.comp NR.symm
  let CN := gammaNativeElementaryChart (hc := hc) hκ hs h00 hr A hFull (Fin.last n) hAd
  let Cone := gammaGroundMeasuredRVPositive hc B
  let r := (gammaMeasuredPointProductProjection U).comp RT.bijection
  let targetMap := (gammaGroundRVPackBijection U.underlying.domain Cone.underlying.domain).comp
    ((r.prodMap (GammaGroundBijection.id Cone.underlying.domain)).comp CN)
  let targetHom : GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaElementaryAt hκ hs h00 hr A (Fin.last n) hAd)
        (Ω.comp (gammaNativeElementaryOldLabel hκ hs h00 hr A (Fin.last n) hAd)))
      (U.product Cone) := by
    refine ⟨targetMap,?_⟩
    intro w
    let z := CN.map w
    let a : (Section5.nativeRVGroundDomain (hc := hc) A) := ⟨z.val.1,z.property.1⟩
    let b : Cone.underlying.domain := ⟨z.val.2,z.property.2⟩
    have hN := gammaNativeElementary_weight hκ hs h00 hr A hFull Ω (Fin.last n) hAd w
    have hR := (RT.preserves a).trans (gammaMeasuredPointProduct_weight U (RT.bijection.map a))
    change _ = (U.product Cone).combinedWeight (gammaGroundRVPackPair U.underlying.domain Cone.underlying.domain (r.map a) b)
    rw [GammaGroundMeasuredRVObject.product_combined_pair]
    exact hN.trans (congrArg (fun v => v * Cone.combinedWeight b) hR)
  have hPoint := gammaGroundMeasuredRVProductHom (GammaGroundMeasuredRVHom.id U) (gammaMeasuredPointZeroArityHom hc B)
  exact (GammaMeasuredGeometricRelation.iso ⟨asIso hPoint.symm⟩).trans
    ((GammaMeasuredGeometricRelation.iso ⟨asIso sourceIso.symm⟩).trans
      ((GammaMeasuredGeometricRelation.elementary A Ω (Fin.last n) hAd).trans
        (GammaMeasuredGeometricRelation.iso ⟨asIso targetHom⟩)))

end DiamondIntegral.Section3
