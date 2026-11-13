import «section 4».IntrinsicBalancedSpecialClasses
import «section 4».RESWeightEmbedding
import «section 4».RVMeasuredPDegreeZero

/-! The homogeneous P quotient of the intrinsic full balanced tensor.
Comparison and both measured evaluations factor through it, and the
latter are surjective. This source quotient is nontrivial; no degree-one
point nonvanishing or global RV descent is inferred. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.IntrinsicBalancedPQuotient
open IntrinsicBalancedTensors IntrinsicBalancedSpecialClasses IntrinsicFiniteGammaAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pIdeal (B : Base (M := M)) : Ideal (Source B) := Ideal.span {pPreimage B}

theorem ideal_homogeneous (B : Base (M := M)) : (pIdeal B).IsHomogeneous (IntrinsicBalancedGradings.measuredPiece B) := by
  apply Ideal.homogeneous_span
  intro x hx
  have he : x = pPreimage B := hx
  subst x
  exact ⟨1, pPreimage_mem B⟩

def Ring (B : Base (M := M)) := Source B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : Source B →+* Ring B := Ideal.Quotient.mk _

theorem p_zero (B : Base (M := M)) : quotient B (pPreimage B) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem ideal_coefficients (B : Base (M := M)) : ∀ n x, x ∈ pIdeal B →
    ((IntrinsicBalancedGradings.measuredCoaction B).map x).coeff n ∈ pIdeal B :=
  (IntrinsicBalancedGradings.measuredCoaction B).homogeneous_ideal_coefficients _ (ideal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (IntrinsicBalancedGradings.measuredCoaction B).quotient _ (ideal_coefficients B)
def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

def comparisonRaw (B : Base (M := M)) : Source B →+* RVDisjointPQuotients.Measured.Ring B :=
  (RVDisjointPQuotients.Measured.quotient B).comp (IntrinsicBalancedTensors.comparison B).toRingHom

theorem comparison_ideal_zero (B : Base (M := M)) : pIdeal B ≤ RingHom.ker (comparisonRaw B) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = pPreimage B := hx
  subst x
  change RVDisjointPQuotients.Measured.quotient B (IntrinsicBalancedTensors.comparison B (pPreimage B)) = 0
  rw [comparison_pPreimage]
  exact RVDisjointPQuotients.Measured.p_zero B

def comparison (B : Base (M := M)) : Ring B →+* RVDisjointPQuotients.Measured.Ring B :=
  Ideal.Quotient.lift _ (comparisonRaw B) (comparison_ideal_zero B)

theorem comparison_mem (B : Base (M := M)) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    comparison B x ∈ IntrinsicQuotientGradings.MeasuredP.piece B n :=
  (IntrinsicBalancedGradings.measuredCoaction B).quotientLift_mem (IntrinsicQuotientGradings.MeasuredP.coaction B)
    (comparisonRaw B) (pIdeal B) (ideal_coefficients B) (comparison_ideal_zero B)
    (fun _ _ hy => IntrinsicQuotientGradings.MeasuredP.quotient_mem B (IntrinsicBalancedGradings.comparison_mem B hy)) hx

theorem target_zero_ne_one (B : Base (M := M)) : (0 : RESDisjointReduction.Measured.Ring B) ≠ 1 := by
  intro h
  apply RESWeightEmbedding.reduced_zero_ne_one B
  have he := congrArg (RESDisjointReduction.Measured.equivalence B) h
  simpa only [map_zero, map_one] using he


theorem zero_ne_one (B : Base (M := M)) : (0 : Ring B) ≠ 1 := by
  intro h
  apply RVMeasuredPDegreeZero.zero_ne_one B
  have he := congrArg ((RVDisjointPQuotients.Measured.equivalence B).toRingHom.comp (comparison B)) h
  simpa only [map_zero, map_one] using he

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_ideal_zero (k : EulerKind) : pIdeal B ≤ RingHom.ker (IntrinsicBalancedEvaluations.measured h00 linear hκ hs B hr hγ hΓ k) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = pPreimage B := hx
  subst x
  exact evaluation_pPreimage h00 linear hκ hs B hr hγ hΓ k

def evaluation (k : EulerKind) : Ring B →+* RESDisjointReduction.Measured.Ring B :=
  Ideal.Quotient.lift _ (IntrinsicBalancedEvaluations.measured h00 linear hκ hs B hr hγ hΓ k)
    (evaluation_ideal_zero h00 linear hκ hs B hr hγ hΓ k)

theorem evaluation_mem (k : EulerKind) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k x ∈ IntrinsicQuotientGradings.MeasuredRES.piece B n :=
  (IntrinsicBalancedGradings.measuredCoaction B).quotientLift_mem (IntrinsicQuotientGradings.MeasuredRES.coaction B)
    (IntrinsicBalancedEvaluations.measured h00 linear hκ hs B hr hγ hΓ k) (pIdeal B) (ideal_coefficients B)
    (evaluation_ideal_zero h00 linear hκ hs B hr hγ hΓ k)
    (fun _ _ hy => IntrinsicBalancedEvaluations.measured_mem h00 linear hκ hs B hr hγ hΓ k hy) hx

theorem evaluation_res (k : EulerKind) (x : RESDisjointPresentation.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (quotient B (x ⊗ₜ[Coeff B] 1)) = RESDisjointReduction.Measured.quotient B x :=
  IntrinsicBalancedEvaluations.measured_on_res h00 linear hκ hs B hr hγ hΓ k x

theorem evaluation_surjective (k : EulerKind) : Function.Surjective (evaluation h00 linear hκ hs B hr hγ hΓ k) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨quotient B (x ⊗ₜ[Coeff B] 1), evaluation_res h00 linear hκ hs B hr hγ hΓ k x⟩


end DiamondIntegral.Section4.IntrinsicBalancedPQuotient
