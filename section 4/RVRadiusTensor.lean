import «section 4».RVBoundedTensor

/-! An explicit integer-tensor preimage of every accepted radius class
has zero constructed evaluation. This is a preimage calculation; global
descent and finite-Gamma balancing are not inferred from it. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVRadiusTensor
open RVBoundedTensor RVRadiusGenerators GammaRVLifts RVPointChoices
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def annulusChart (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    GammaBoundedRVCharts.BoundedChart B 1 :=
  ⟨GammaRadiusAnnulus.annulusChart B γ hγ, GammaRadiusAnnulus.annulus_bounded γ hγ.1⟩

def radiusPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    (t : RadiusLift B γ) : Source B :=
  (1 ⊗ₜ[ℤ] GammaBoundedRVPresentation.objectClass (annulusChart B γ hγ)) +
    (RESChartRing.objectClass (pointRESChart B t.point t.definable) ⊗ₜ[ℤ] 1) -
    (RESChartRing.objectClass (pointRESChart B oneCode (oneCode_definable B)) ⊗ₜ[ℤ] 1)

theorem comparison_radiusPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    comparison B (radiusPreimage B γ hγ t) = RVRadiusIdeal.radiusGenerator B γ hγ t := by
  unfold radiusPreimage
  simp only [map_sub, map_add, comparison_tmul, map_one, one_mul, mul_one,
    GammaBoundedRVMaps.sharp_class, RVBoundedMaps.ofRES_class]
  rfl

def pGammaPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) : Source B :=
  radiusPreimage B γ hγ (Classical.choice (radiusLift_exists B γ hγ))

theorem comparison_pGammaPreimage (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : comparison B (pGammaPreimage B γ hγ) = RVRadiusIdeal.pGamma B γ hγ :=
  comparison_radiusPreimage B γ hγ _

theorem annulus_evaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ' : γ ∈ admissibleRadii B) :
    GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k
      (GammaBoundedRVPresentation.objectClass (annulusChart B γ hγ')) = 0 := by
  change GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B)
    (GammaBoundedRVMaps.auxiliary B (GammaBoundedRVPresentation.objectClass (annulusChart B γ hγ'))) = 0
  rw [GammaBoundedRVMaps.auxiliary_class]
  exact GammaRadiusAnnulus.specialize_annulus hc h00 linear hκ hs B hr hγ hΓ k γ hγ' (RESOrdinaryReduction.torusClass B)

theorem evaluation_radiusPreimage (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ' : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (radiusPreimage B γ hγ' t) = 0 := by
  unfold radiusPreimage
  simp only [map_sub, map_add, evaluation_tmul, map_one, one_mul, mul_one]
  rw [annulus_evaluation, RESOrdinaryPoints.forget_point_classes B t.point oneCode t.definable (oneCode_definable B), zero_add, sub_self]

theorem evaluation_pGammaPreimage (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ' : γ ∈ admissibleRadii B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (pGammaPreimage B γ hγ') = 0 :=
  evaluation_radiusPreimage hc h00 linear hκ hs B hr hγ hΓ k γ hγ' _

end DiamondIntegral.Section4.RVRadiusTensor
