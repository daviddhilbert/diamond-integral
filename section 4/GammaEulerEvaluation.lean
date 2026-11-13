import «section 4».GammaRVMapGradings
import «section 4».GammaWeightProfiles

/-! The unmeasured Gamma evaluation uses the chosen total Euler
character on the actual profile coefficient. It sends each weighted
chart to chi(I) times T^n and thereby forgets its volume form. Both Euler
choices are retained on unbounded domains. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaEulerEvaluation
open GammaWeightedCharts GammaObjectPolynomial
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def coefficientEuler (B : Base (M := M)) (k : EulerKind) : GammaDefinableConvolution.baseSubring B k →+* ℤ :=
  (EulerFunction.totalEuler k).comp (GammaDefinableConvolution.baseSubring B k).subtype

def polynomial (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R] (t : R) :
    GammaFunctionPolynomial.sourceRing B k →+* R :=
  (Polynomial.eval₂RingHom ((Int.castRingHom R).comp (coefficientEuler B k)) t).comp (GammaFunctionPolynomial.sourceRing B k).subtype

theorem polynomial_chart (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {R : Type*} [CommRing R] (t : R)
    {n : ℕ} (a : Chart B n) : polynomial B k t (chartPolynomial h00 hκ hs B hr hγ k a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : R) * t ^ n := by
  change Polynomial.eval₂ _ t (Polynomial.monomial n
    (profileCoefficient h00 hκ hs B hr hγ k a.support a.support_definable
      a.normalizedVolume a.normalizedVolume_definable)) = _
  rw [Polynomial.eval₂_monomial]
  exact congrArg (fun z : ℤ => (z : R) * t ^ n)
    (GammaWeightProfiles.profile_integral h00 linear hκ hs B hr hγ hΓ k a.support a.support_definable
      a.normalizedVolume a.normalizedVolume_definable)

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {R : Type*} [CommRing R] (t : R) :
    GammaRVChartPresentation.ChartRing B →+* R :=
  (polynomial B k t).comp (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k)

theorem evaluation_class (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {R : Type*} [CommRing R] (t : R)
    {n : ℕ} (a : Chart B n) : evaluation h00 linear hκ hs B hr hγ hΓ k t (GammaRVChartPresentation.objectClass a) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : R) * t ^ n := by
  change polynomial B k t (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k
    (GammaRVChartPresentation.objectClass a)) = _
  unfold GammaRVChartPresentation.objectClass
  rw [GammaRVChartPresentation.interpretation_symbol]
  exact polynomial_chart h00 linear hκ hs B hr hγ hΓ k t a

end DiamondIntegral.Section4.GammaEulerEvaluation
