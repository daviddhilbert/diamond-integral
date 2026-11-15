import «section 5».NativeBoundedRetraction

/-! The monomial evaluation formula in the actual ungraded native target.
The source can carry any finite label and any underlying presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem nativeRVEvaluation_monomial (kind : EulerKind) {k r l : ℕ}
    (X : RVMeasuredCharts.Chart B k) (V : RVMeasuredCharts.RESChart B r)
    (I : GammaOrdinaryCharts.Chart B l)
    (F : RVUnderlyingIsomorphisms.Iso X
      (RVMeasuredProduct.product V.toChart (GammaOrdinaryCharts.sharpChart I))) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass X) =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass V) *
        nativeTorusClass B ^ l *
          (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind l
            (GammaIndicators.indicatorFamily B I.support I.support_definable) : RESDimensionFreeReduction.Ring B) := by
  rw [nativeRVEvaluation_underlyingIso h00 linear hκ hs hc B hr hγ hΓ kind _ _ F,
    RVOrdinaryRing.objectClass_product, map_mul,
    ← RVOrdinaryMaps.ofRES_class B V,
    ← GammaOrdinarySharpRingMap.sharp_class B I,
    nativeRVEvaluation_res, nativeRVEvaluation_gamma]
  ring

theorem nativeRVEvaluation_relative_monomial (kind : EulerKind) {k j r l m : ℕ}
    (X : RVMeasuredCharts.Chart B k) (Y : RVMeasuredCharts.Chart B j)
    (V : RVMeasuredCharts.RESChart B r)
    (I : GammaOrdinaryCharts.Chart B m) (K : GammaOrdinaryCharts.Chart B (m + l))
    (F : RVUnderlyingIsomorphisms.Iso X
      (RVMeasuredProduct.product V.toChart (GammaOrdinaryCharts.sharpChart I)))
    (G : RVUnderlyingIsomorphisms.Iso Y
      (RVMeasuredProduct.product V.toChart (GammaOrdinaryCharts.sharpChart K)))
    (e : ℤ)
    (hχ : GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind (m + l)
        (GammaIndicators.indicatorFamily B K.support K.support_definable) =
      e * GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ kind m
        (GammaIndicators.indicatorFamily B I.support I.support_definable)) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass Y) =
      nativeTorusClass B ^ l * e *
        nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass X) := by
  rw [nativeRVEvaluation_monomial h00 linear hκ hs hc B hr hγ hΓ kind _ _ _ G,
    nativeRVEvaluation_monomial h00 linear hκ hs hc B hr hγ hΓ kind _ _ _ F,
    hχ, Int.cast_mul, pow_add]
  ring

end DiamondIntegral.Section5
