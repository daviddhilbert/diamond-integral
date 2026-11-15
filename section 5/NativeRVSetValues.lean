import «section 5».GammaRVSetObjects
import «section 5».NativeBoundedRetraction
import «section 3».GammaGroundRVUnitRES

/-! Arbitrary original-ground RV domains have actual finite labels and
native bounded values, invariant under every underlying domain bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeRVObjectOfGammaSet {n : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundRVObject hc B n where
  arity := n
  domain := A
  volume := gammaGroundCleanRVMap hc B A
  finite := gammaGroundCleanRVMap_finite hc B A
  nonzero := by
    intro a i
    simpa only [gammaGroundCleanRVMap, GammaGroundMap.restrict, GammaGroundMap.comp,
      GammaGroundMap.inclusion, GammaGroundMap.ofReal, cleanRVMap, Map.ofCodes_apply] using
      cleanRV_nonzero a.val i

def nativeRVObjectUnderlyingIso {k l : ℕ} {U : GammaGroundRVObject hc B k} {V : GammaGroundRVObject hc B l}
    (f : GammaGroundBijection U.domain V.domain) :
    RVUnderlyingIsomorphisms.Iso (Section3RVChartBridge.chart U) (Section3RVChartBridge.chart V) :=
  RVUnderlyingIsomorphisms.ofMap _ _ (Section3RVCodeBridge.rawMap f.map)
    (Section3RVCodeBridge.rawMap_definable f.map) (Section3RVCodeBridge.rawMap_bijective f.map f.bijective)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

def nativeRVSetValue {n : ℕ} (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    RESDimensionFreeReduction.Ring B :=
  nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
    (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (nativeRVObjectOfGammaSet A)))

def nativeUnitRVSetValue {n : ℕ} (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    RESDimensionFreeReduction.Ring B :=
  nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (gammaGroundRVUnitToRVMap A).image

theorem nativeRVSetValue_bijection {n m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (f : GammaGroundBijection A C) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C :=
  nativeRVEvaluation_underlyingIso h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (nativeRVObjectUnderlyingIso (U := nativeRVObjectOfGammaSet A) (V := nativeRVObjectOfGammaSet C) f)

theorem nativeUnitRVSetValue_bijection {n m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) (f : GammaGroundBijection A C) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C :=
  nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    ((gammaGroundRVUnitPresentationBijection C).comp (f.comp (gammaGroundRVUnitPresentationBijection A).symm))

end DiamondIntegral.Section5
