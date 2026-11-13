import «section 4».RVCoefficientCoordinateTranslationKernel
import «section 4».RVOrdinaryTranslationIdeal
import «section 4».RVOrdinaryBoundedTensorForget

/-! The coefficient-coordinate translation isomorphism lives inside the
bounded RV category when the Gamma factor is bounded. The resulting
homogeneous ideal lies in its comparison kernel. Both direct ordinary
Euler maps kill these relations without a canonical-structure premise. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBoundedCoefficientCoordinateTranslationKernel
open RVMeasuredCharts RVTranslationIdeals RVBalancedGradings RVCoordinateScaling
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem comparison_generator_zero (B : Base (M := M)) {k n : ℕ} (r : RESChart B k) (j : Fin r.arity) (i : Fin n)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (x j) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (c : GammaBoundedRVCharts.BoundedChart B n) :
    RVBoundedBalancedTensor.comparison B (boundedGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c) = 0 := by
  let d := GammaBoundedTranslationCharts.translatedChart B (shiftVector i δ) (shiftVector_definable B i δ hδ) c
  have h := RVBoundedRing.objectClass_iso
    (a := RVBoundedCharts.product (RVBoundedCharts.ofRES r) (GammaBoundedRVCharts.sharp c))
    (b := RVBoundedCharts.product (RVBoundedCharts.ofRES r) (GammaBoundedRVCharts.sharp d))
    (RVCoefficientCoordinateTranslation.iso B r.toChart j i hp δ hv hδ c.toChart)
  rw [RVBoundedRing.objectClass_product, RVBoundedRing.objectClass_product] at h
  unfold boundedGenerator
  rw [map_sub, RVBoundedBalancedTensor.comparison_tmul, RVBoundedBalancedTensor.comparison_tmul,
    RVBoundedMaps.ofRES_class]
  have hc : GammaBoundedRVMaps.sharp B (GammaBoundedRVPresentation.objectClass c) =
      RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp c) := GammaBoundedRVMaps.sharp_class B c
  have hd : GammaBoundedRVMaps.sharp B (GammaBoundedRVPresentation.objectClass d) =
      RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp d) := GammaBoundedRVMaps.sharp_class B d
  change RVBoundedRing.objectClass (RVBoundedCharts.ofRES r) *
      GammaBoundedRVMaps.sharp B (GammaBoundedRVPresentation.objectClass c) -
    RVBoundedRing.objectClass (RVBoundedCharts.ofRES r) *
      GammaBoundedRVMaps.sharp B (GammaBoundedRVPresentation.objectClass d) = 0
  rw [hc, hd]
  exact sub_eq_zero.mpr h

def coefficientIdeal (B : Base (M := M)) : Ideal (RVBoundedBalancedTensor.Source B) :=
  Ideal.span {x | ∃ k n, ∃ r : RESChart B k, ∃ j : Fin r.arity, ∃ i : Fin n,
    ∃ hp : ∀ u ∈ r.domain, NonzeroRV (u j), ∃ δ : Values.Gamma (M := M),
    ∃ hv : ∀ u ∈ r.domain, codeValue (u j) = δ, ∃ hδ : GammaDefinableClosureAtBase B δ,
    ∃ c : GammaBoundedRVCharts.BoundedChart B n,
      x = boundedGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c}

theorem coefficientIdeal_le_comparison_ker (B : Base (M := M)) :
    coefficientIdeal B ≤ RingHom.ker (RVBoundedBalancedTensor.comparison B).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact comparison_generator_zero B r j i hp δ hv hδ c

theorem coefficientIdeal_homogeneous (B : Base (M := M)) :
    (coefficientIdeal B).IsHomogeneous (boundedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact ⟨k + n, (boundedPiece B (k + n)).sub_mem
    (bounded_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B r) (GammaBoundedRVGrading.class_mem B c))
    (bounded_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B r) (GammaBoundedRVGrading.class_mem B _))⟩

theorem forget_generator (B : Base (M := M)) {m n : ℕ} (r : RESChart B m)
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaBoundedRVCharts.BoundedChart B n) :
    RVOrdinaryBoundedTensorForget.forget B (boundedGenerator B r a ha c) =
      RVOrdinaryTranslationIdeal.generator B r a ha (GammaOrdinaryCharts.ofWeighted c.toChart) := by
  unfold boundedGenerator RVOrdinaryTranslationIdeal.generator
  rw [map_sub, RVOrdinaryBoundedTensorForget.forget_tmul, RVOrdinaryBoundedTensorForget.forget_tmul,
    RESOrdinaryRing.forget_objectClass, GammaBoundedRVMaps.forget_class, GammaBoundedRVMaps.forget_class,
    GammaOrdinaryRing.forget_class, GammaOrdinaryRing.forget_class]
  rfl

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_generator_zero (kind : EulerKind) {m n : ℕ} (r : RESChart B m)
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaBoundedRVCharts.BoundedChart B n) :
    RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ kind (boundedGenerator B r a ha c) = 0 := by
  have he := RingHom.congr_fun (RVOrdinaryBoundedTensorForget.evaluation_square h00 linear hκ hs B hr hγ hΓ kind)
    (boundedGenerator B r a ha c)
  change RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind
    (RVOrdinaryBoundedTensorForget.forget B (boundedGenerator B r a ha c)) = _ at he
  rw [forget_generator] at he
  exact he.symm.trans (RVOrdinaryTranslationIdeal.evaluation_generator_zero h00 linear hκ hs B hr hγ hΓ kind
    r a ha (GammaOrdinaryCharts.ofWeighted c.toChart))

theorem coefficientIdeal_le_evaluation_ker (kind : EulerKind) :
    coefficientIdeal B ≤ RingHom.ker (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact evaluation_generator_zero h00 linear hκ hs B hr hγ hΓ kind r (shiftVector i δ) (shiftVector_definable B i δ hδ) c

end DiamondIntegral.Section4.RVBoundedCoefficientCoordinateTranslationKernel
