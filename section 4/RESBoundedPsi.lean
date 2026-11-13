import «section 4».RESOrdinaryReduction
import «section 4».GammaBoundedSpecialization
import «section 4».GammaBoundedChartComparison

/-! The bounded polynomial source and bounded Gamma chart subring map to
the concrete ordinary RES quotient, with the actual torus class as T.
The map ignores volume weights and is independent of the Euler choice.
Grading/category identification and RV tensor descent remain open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESBoundedPsi
open RESOrdinaryReduction GammaBoundedFunctions GammaDefinableEuler

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def psi (B : Base (M := M)) (k : EulerKind) : GammaBoundedPolynomial.sourceRing B k →+* ReducedRing B :=
  GammaBoundedSpecialization.specialize B k (torusClass B)

theorem psi_point (B : Base (M := M)) (k : EulerKind) (n : ℕ) (a : Name B) :
    psi B k (GammaBoundedSpecialization.pointMonomial B k n a) = (torusClass B) ^ n :=
  GammaBoundedSpecialization.specialize_point B k (torusClass B) n a

theorem psi_interval (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) (a : Name B) :
    psi B k (GammaBoundedSpecialization.intervalMonomial B k n hn a) = -((torusClass B) ^ n) :=
  GammaBoundedSpecialization.specialize_interval B k (torusClass B) n hn a

theorem psi_object (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaOrderLogic.GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : GammaDefinableMaps.MapDefinable B μ)
    (hbox : GammaBoundedProducts.DomainBounded I) :
    psi B k (GammaBoundedObjectPolynomial.objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k n I hI μ hμ hbox) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B I hI) : ReducedRing B) *
        (torusClass B) ^ n :=
  GammaBoundedSpecialization.specialize_object hc h00 linear hκ hs B hr hγ hΓ k n I hI μ hμ hbox (torusClass B)

def chartMap (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaBoundedChartMap.boundedChartSubring B →+* ReducedRing B :=
  GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k (torusClass B)

theorem chartMap_boundedClass (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a : GammaWeightedCharts.Chart B n) (ha : GammaBoundedProducts.DomainBounded a.support) :
    chartMap hc h00 linear hκ hs B hr hγ hΓ k (GammaBoundedChartMap.boundedClass a ha) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : ReducedRing B) * (torusClass B) ^ n :=
  GammaBoundedChartMap.specialize_boundedClass hc h00 linear hκ hs B hr hγ hΓ k a ha (torusClass B)

theorem chartMap_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    chartMap hc h00 linear hκ hs B hr hγ hΓ k = chartMap hc h00 linear hκ hs B hr hγ hΓ l :=
  GammaBoundedChartComparison.specialize_independent_kind hc h00 linear hκ hs B hr hγ hΓ k l (torusClass B)

theorem psi_point_fibre (B : Base (M := M)) (k : EulerKind) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    psi B k (GammaBoundedSpecialization.pointMonomial B k 1
      ⟨toPaperGamma (α * β), GammaGroupNames.mul_definable_base B α β hα hβ⟩) =
      forget B (RESChartRing.objectClass (RESFibreObjects.fibre B α β hα hβ)) := by
  have h := psi_point B k 1 ⟨toPaperGamma (α * β), GammaGroupNames.mul_definable_base B α β hα hβ⟩
  exact h.trans ((pow_one _).trans (forget_fibre B α β hα hβ).symm)

end DiamondIntegral.Section4.RESBoundedPsi
