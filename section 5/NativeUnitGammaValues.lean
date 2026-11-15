import «section 5».NativeRVSetArithmetic
import «section 3».RVUnitGammaCodeBijection
import «section 4».Section3GammaRVCodeBridge

/-! The native bounded value of a full nonzero RV value preimage is its
actual Gamma Euler integral times every retained residue-torus factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem nativeUnitRVSetValue_gamma {n : ℕ}
    (I : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n))) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (gammaGroundRVUnitGammaPreimage I) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind n
        (GammaIndicators.indicatorFamily B I.carrier (Section3GammaChartBridge.chart I).support_definable) :
          RESDimensionFreeReduction.Ring B) * nativeTorusClass B ^ n := by
  let a := Section3GammaChartBridge.chart I
  let U := gammaGroundGammaRVCodeLift I
  have hd : (Section3RVChartBridge.chart U).domain = (GammaOrdinaryCharts.sharpChart a).domain :=
    Section3GammaRVCodeBridge.rawDomain_codeLift I
  let f : RVUnderlyingIsomorphisms.Iso (Section3RVChartBridge.chart U) (GammaOrdinaryCharts.sharpChart a) :=
    RVUnderlyingIsomorphisms.ofMap _ _ id
      (RVSharpCharts.identity_graph_definable B _ (Section3RVChartBridge.chart U).domain_definable)
      (by rw [hd]; exact Set.bijOn_id _)
  calc
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (gammaGroundRVUnitGammaPreimage I) =
        nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) :=
      nativeUnitRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ kind _ U (gammaGroundRVUnitGammaCodeBijection I)
    _ = nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) :=
      nativeGroundRVEvaluation_class h00 linear hκ hs hc B hr hγ hΓ kind U
    _ = nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (RVOrdinaryRing.objectClass (GammaOrdinaryCharts.sharpChart a)) :=
      nativeRVEvaluation_underlyingIso h00 linear hκ hs hc B hr hγ hΓ kind _ _ f
    _ = _ := by
      rw [← GammaOrdinarySharpRingMap.sharp_class]
      exact nativeRVEvaluation_gamma h00 linear hκ hs hc B hr hγ hΓ kind a

end DiamondIntegral.Section5
