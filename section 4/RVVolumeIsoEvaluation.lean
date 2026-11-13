import «section 4».RVFiniteBalancedTensor
import «section 4».RVBoundedBalancedTensor

/-! Both constructed evaluations identify Gamma charts related by an
actual definable volume-preserving bijection, without assuming that this
bijection has an RV lift. The corresponding tensor differences therefore
vanish under evaluation. This does not identify the comparison kernel. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVVolumeIsoEvaluation
open GammaWeightedCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem unbounded_gamma_eq (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a b : Chart B n) (F : VolumeIso a b) :
    GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k (GammaRVChartPresentation.objectClass a) =
      GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k (GammaRVChartPresentation.objectClass b) := by
  change RESUnboundedPsi.psi B k (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k
    (GammaRVChartPresentation.objectClass a)) = RESUnboundedPsi.psi B k
      (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k (GammaRVChartPresentation.objectClass b))
  apply congrArg (RESUnboundedPsi.psi B k)
  unfold GammaRVChartPresentation.objectClass
  rw [GammaRVChartPresentation.interpretation_symbol, GammaRVChartPresentation.interpretation_symbol]
  exact chartPolynomial_volumeIso h00 linear hκ hs B hr hγ hΓ k a b F

theorem bounded_auxiliary_eq (B : Base (M := M)) {n : ℕ}
    (a b : GammaBoundedRVCharts.BoundedChart B n) (F : VolumeIso a.toChart b.toChart) :
    GammaBoundedRVMaps.auxiliary B (GammaBoundedRVPresentation.objectClass a) =
      GammaBoundedRVMaps.auxiliary B (GammaBoundedRVPresentation.objectClass b) := by
  rw [GammaBoundedRVMaps.auxiliary_class, GammaBoundedRVMaps.auxiliary_class]
  apply Subtype.ext
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (GammaChartPresentation.relationIdeal B) (GammaChartPresentation.symbol a.toChart) -
    Ideal.Quotient.mk (GammaChartPresentation.relationIdeal B) (GammaChartPresentation.symbol b.toChart) = 0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (GammaChartPresentation.Relation.iso a.toChart b.toChart F))

theorem bounded_gamma_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a b : GammaBoundedRVCharts.BoundedChart B n) (F : VolumeIso a.toChart b.toChart) :
    GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k (GammaBoundedRVPresentation.objectClass a) =
      GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k (GammaBoundedRVPresentation.objectClass b) :=
  congrArg (GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryReduction.torusClass B))
    (bounded_auxiliary_eq B a b F)

theorem unbounded_tensor_difference (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (r : RESChartRing.Ring B) (a b : Chart B n) (F : VolumeIso a b) :
    RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k
      (r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaRVChartPresentation.objectClass a -
        r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaRVChartPresentation.objectClass b) = 0 := by
  rw [map_sub, RVFiniteBalancedTensor.evaluation_tmul, RVFiniteBalancedTensor.evaluation_tmul,
    unbounded_gamma_eq h00 linear hκ hs B hr hγ hΓ k a b F, sub_self]

theorem bounded_tensor_difference (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (r : RESChartRing.Ring B) (a b : GammaBoundedRVCharts.BoundedChart B n) (F : VolumeIso a.toChart b.toChart) :
    RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k
      (r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaBoundedRVPresentation.objectClass a -
        r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaBoundedRVPresentation.objectClass b) = 0 := by
  rw [map_sub, RVBoundedBalancedTensor.evaluation_tmul, RVBoundedBalancedTensor.evaluation_tmul,
    bounded_gamma_eq hc h00 linear hκ hs B hr hγ hΓ k a b F, sub_self]

end DiamondIntegral.Section4.RVVolumeIsoEvaluation
