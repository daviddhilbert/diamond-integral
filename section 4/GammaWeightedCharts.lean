import «section 4».GammaObjectRelations

/-! Concrete weighted Gamma charts with volume forms definable only on
their actual domains. Their polynomial assignment is independent of the
extension and respects actual volume-preserving definable bijections.
Finite disjoint unions and the manuscript's additional RV-lift condition
on Gamma morphisms remain category-presentation obligations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaWeightedCharts
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaObjectPolynomial GammaObjectRelations
open GammaMeasuredProfileInvariance GammaProfileRestrictions GammaBijectiveRelations

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Chart (B : Base (M := M)) (n : ℕ) where
  support : Set (Fin n → Values.Gamma (M := M))
  support_definable : GammaDefinable B support
  volume : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)
  volume_definable : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
    Fin.tail z ∈ support ∧ z 0 = volume (Fin.tail z)}

def Chart.normalizedVolume {B : Base (M := M)} {n : ℕ} (a : Chart B n) :
    (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) := extendWeight a.support a.volume

theorem Chart.normalizedVolume_definable {B : Base (M := M)} {n : ℕ} (a : Chart B n) :
    MapDefinable B a.normalizedVolume :=
  extendWeight_definable B a.support a.support_definable a.volume a.volume_definable

theorem Chart.normalizedVolume_on {B : Base (M := M)} {n : ℕ} (a : Chart B n)
    (u : Fin n → Values.Gamma (M := M)) (hu : u ∈ a.support) : a.normalizedVolume u = a.volume u := by
  simp only [Chart.normalizedVolume, extendWeight, ite_eq_left hu]

structure VolumeIso {B : Base (M := M)} {n : ℕ} (a b : Chart B n) where
  map : (Fin n → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M))
  graph_definable : GammaDefinable B (graphOn a.support map)
  bijective : Set.BijOn map a.support b.support
  volume_eq : ∀ u ∈ a.support, a.volume u = b.volume (map u) * (∏ i, map u i) / (∏ i, u i)

def chartPolynomial (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (a : Chart B n) : GammaFunctionPolynomial.sourceRing B k :=
  objectPolynomial h00 hκ hs B hr hγ k n a.support a.support_definable
    a.normalizedVolume a.normalizedVolume_definable

theorem chartPolynomial_volumeIso (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a b : Chart B n) (F : VolumeIso a b) :
    chartPolynomial h00 hκ hs B hr hγ k a = chartPolynomial h00 hκ hs B hr hγ k b := by
  apply objectPolynomial_volume_bijOn h00 linear hκ hs B hr hγ hΓ k n
    a.support b.support a.support_definable b.support_definable
    a.normalizedVolume b.normalizedVolume a.normalizedVolume_definable b.normalizedVolume_definable
    F.map F.graph_definable F.bijective
  intro u hu
  rw [a.normalizedVolume_on u hu, b.normalizedVolume_on (F.map u) (F.bijective.mapsTo hu)]
  exact F.volume_eq u hu

end DiamondIntegral.Section4.GammaWeightedCharts
