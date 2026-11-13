import «section 4».GammaChartPresentation
import «section 4».GammaUnboundedAssignments

/-! Compose the actual chart quotient homomorphism with the unbounded
source specialization. The counterweighted ray is evaluated through this
constructed ring homomorphism; the target RES realization remains open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaChartSpecializations
open GammaOrderLogic GammaDefinableMaps GammaWeightedCharts GammaChartOperations GammaChartPresentation
open GammaNamesSubgroup GammaUnboundedAssignments GammaCounterweightedRay

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def specialize (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    {R : Type*} [CommRing R] (u : Multiplicative (additiveNames B) →* R) (T : R) : ChartRing B →+* R :=
  (GammaUnboundedSpecialization.specialize B k u T).comp (interpretation h00 linear hκ hs B hr hγ hΓ k)

theorem specialize_ofTotal (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    {R : Type*} [CommRing R] (u : Multiplicative (additiveNames B) →* R) (T : R) :
    specialize h00 linear hκ hs B hr hγ hΓ k u T
      (Ideal.Quotient.mk (relationIdeal B) (symbol (ofTotal B n I hI μ hμ))) =
    GammaUnboundedSpecialization.specialize B k u T (GammaObjectPolynomial.objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ) := by
  exact congrArg (GammaUnboundedSpecialization.specialize B k u T)
    ((interpretation_symbol h00 linear hκ hs B hr hγ hΓ k (ofTotal B n I hI μ hμ)).trans
      (chartPolynomial_ofTotal h00 hκ hs B hr hγ k n I hI μ hμ))

def counterweightedRayClass (B : Base (M := M)) : ChartRing B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol
    (ofTotal B 1 positiveRay (positiveRay_definable B) inverseCoordinate (inverseCoordinate_definable B)))

theorem geometric_counterweightedRay (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T Q : R) (hA : Q + T = 0) :
    specialize h00 linear hκ hs B hr hγ hΓ EulerKind.geometric u T (counterweightedRayClass B) = Q := by
  change specialize h00 linear hκ hs B hr hγ hΓ EulerKind.geometric u T
    (Ideal.Quotient.mk (relationIdeal B) (symbol _)) = Q
  rw [specialize_ofTotal]
  exact specialize_counterweighted_geometric h00 hκ hs B hr hγ u T Q hA

theorem bounded_counterweightedRay (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {R : Type*} [CommRing R]
    (u : Multiplicative (additiveNames B) →* R) (T : R) :
    specialize h00 linear hκ hs B hr hγ hΓ EulerKind.bounded u T (counterweightedRayClass B) = 0 := by
  change specialize h00 linear hκ hs B hr hγ hΓ EulerKind.bounded u T
    (Ideal.Quotient.mk (relationIdeal B) (symbol _)) = 0
  rw [specialize_ofTotal]
  exact specialize_counterweighted_bounded h00 hκ hs B hr hγ u T

end DiamondIntegral.Section4.GammaChartSpecializations
