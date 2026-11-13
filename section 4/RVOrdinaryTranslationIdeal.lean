import «section 4».GammaOrdinaryTranslations
import «section 4».RVOrdinaryTensorForget
import «section 4».RVTranslationIdeals

/-! Both Euler maps on the actual ordinary tensor kill all numerical
Gamma-translation differences, even when the constants have no definable
RV lifts. This homogeneous evaluation ideal is not claimed to be the
whole RV comparison kernel. Measured translation differences forget to
these ordinary differences. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryTranslationIdeal
open RVOrdinaryBalancedTensor GammaOrdinaryAlgebras GammaOrdinaryTranslations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def generator (B : Base (M := M)) {m n : ℕ} (r : RVMeasuredCharts.RESChart B m)
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaOrdinaryCharts.Chart B n) : Source B :=
  RESOrdinaryRing.objectClass r ⊗ₜ[Coeff B] GammaOrdinaryRing.objectClass c -
    RESOrdinaryRing.objectClass r ⊗ₜ[Coeff B] GammaOrdinaryRing.objectClass (translatedChart B a ha c)

def translationIdeal (B : Base (M := M)) : Ideal (Source B) :=
  Ideal.span {x | ∃ m n, ∃ r : RVMeasuredCharts.RESChart B m,
    ∃ a : Fin n → Values.Gamma (M := M), ∃ ha : ∀ i, GammaDefinableClosureAtBase B (a i),
    ∃ c : GammaOrdinaryCharts.Chart B n, x = generator B r a ha c}

theorem translationIdeal_homogeneous (B : Base (M := M)) :
    (translationIdeal B).IsHomogeneous (RVOrdinaryBalancedGradings.piece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨m, n, r, a, ha, c, rfl⟩
  exact ⟨m + n, (RVOrdinaryBalancedGradings.piece B (m + n)).sub_mem
    (RVOrdinaryBalancedGradings.tmul_mem B (RESOrdinaryGrading.class_mem B r) (GammaOrdinaryGrading.class_mem B c))
    (RVOrdinaryBalancedGradings.tmul_mem B (RESOrdinaryGrading.class_mem B r) (GammaOrdinaryGrading.class_mem B _))⟩

theorem forget_generator (B : Base (M := M)) {m n : ℕ} (r : RVMeasuredCharts.RESChart B m)
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaWeightedCharts.Chart B n) :
    RVOrdinaryTensorForget.forget B (RVTranslationIdeals.measuredGenerator B r a ha c) =
      generator B r a ha (GammaOrdinaryCharts.ofWeighted c) := by
  unfold RVTranslationIdeals.measuredGenerator generator
  rw [map_sub, RVOrdinaryTensorForget.forget_tmul, RVOrdinaryTensorForget.forget_tmul,
    RESOrdinaryRing.forget_objectClass, GammaOrdinaryRing.forget_class, GammaOrdinaryRing.forget_class,
    ofWeighted_translated]

theorem map_measuredIdeal_le (B : Base (M := M)) :
    Ideal.map (RVOrdinaryTensorForget.forget B) (RVTranslationIdeals.measuredIdeal B) ≤ translationIdeal B := by
  rw [RVTranslationIdeals.measuredIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro x ⟨y, ⟨m, n, r, a, ha, c, rfl⟩, rfl⟩
  rw [forget_generator]
  exact Ideal.subset_span ⟨m, n, r, a, ha, GammaOrdinaryCharts.ofWeighted c, rfl⟩

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_generator_zero (kind : EulerKind) {m n : ℕ} (r : RVMeasuredCharts.RESChart B m)
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaOrdinaryCharts.Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ kind (generator B r a ha c) = 0 := by
  unfold generator
  rw [map_sub, evaluation_tmul, evaluation_tmul, resEvaluation_translated, sub_self]

theorem translationIdeal_le_evaluation_ker (kind : EulerKind) :
    translationIdeal B ≤ RingHom.ker (evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨m, n, r, a, ha, c, rfl⟩
  exact evaluation_generator_zero h00 linear hκ hs B hr hγ hΓ kind r a ha c

end DiamondIntegral.Section4.RVOrdinaryTranslationIdeal
