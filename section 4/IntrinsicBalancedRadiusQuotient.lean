import «section 4».IntrinsicBalancedSpecialClasses
import «section 4».RVBalancedRadiusQuotient

/-! The actual accepted radius ideal and graded source quotient on the
intrinsic bounded tensor. Comparison and ordinary evaluation factor
through this ideal; this is not descent through the full RV kernel. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.IntrinsicBalancedRadiusQuotient
open IntrinsicBalancedTensors IntrinsicBalancedSpecialClasses IntrinsicFiniteGammaAlgebras GammaRVLifts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def radiusIdeal (B : Base (M := M)) : Ideal (BoundedSource B) :=
  Ideal.span {x | ∃ γ : Values.Gamma (M := M), ∃ hγ : γ ∈ admissibleRadii B, x = radiusPreimage B γ hγ}

theorem ideal_homogeneous (B : Base (M := M)) : (radiusIdeal B).IsHomogeneous (IntrinsicBalancedGradings.boundedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨γ, hγ, rfl⟩
  exact ⟨1, radiusPreimage_mem B γ hγ⟩

theorem map_ideal (B : Base (M := M)) :
    (radiusIdeal B).map (boundedEquivalence B).toAlgHom.toRingHom = RVBalancedRadiusIdeal.radiusIdeal B := by
  rw [radiusIdeal, RVBalancedRadiusIdeal.radiusIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, (boundedEquivalence B).apply_symm_apply _⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨radiusPreimage B γ hγ, ⟨γ, hγ, rfl⟩, (boundedEquivalence B).apply_symm_apply _⟩

def Ring (B : Base (M := M)) := BoundedSource B ⧸ radiusIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : BoundedSource B →+* Ring B := Ideal.Quotient.mk _

theorem ideal_coefficients (B : Base (M := M)) : ∀ n x, x ∈ radiusIdeal B →
    ((IntrinsicBalancedGradings.boundedCoaction B).map x).coeff n ∈ radiusIdeal B :=
  (IntrinsicBalancedGradings.boundedCoaction B).homogeneous_ideal_coefficients _ (ideal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (IntrinsicBalancedGradings.boundedCoaction B).quotient _ (ideal_coefficients B)
def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

def equivalence (B : Base (M := M)) : Ring B ≃+* RVBalancedRadiusQuotient.Ring B :=
  Ideal.quotientEquiv (radiusIdeal B) (RVBalancedRadiusIdeal.radiusIdeal B) (boundedEquivalence B).toRingEquiv (map_ideal B).symm

theorem equivalence_mem_iff (B : Base (M := M)) (n : ℕ) (x : Ring B) :
    equivalence B x ∈ RVBalancedRadiusQuotient.piece B n ↔ x ∈ piece B n :=
  CoactionQuotientEquivalence.mem_iff (IntrinsicBalancedGradings.boundedCoaction B) (RVBalancedGradings.boundedCoaction B)
    (boundedEquivalence B).toRingEquiv (radiusIdeal B) (RVBalancedRadiusIdeal.radiusIdeal B)
    (ideal_coefficients B) (RVBalancedRadiusQuotient.ideal_coefficients B) (map_ideal B).symm
    (fun _ _ hy => IntrinsicBalancedGradings.boundedEquivalence_mem B hy)
    (fun _ _ hy => IntrinsicBalancedGradings.boundedInverse_mem B hy) n x

def comparisonRaw (B : Base (M := M)) : BoundedSource B →+* RVDisjointRadiusQuotient.Ring B :=
  (RVDisjointRadiusQuotient.quotient B).comp (boundedComparison B).toRingHom

theorem comparison_ideal_zero (B : Base (M := M)) : radiusIdeal B ≤ RingHom.ker (comparisonRaw B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  change RVDisjointRadiusQuotient.quotient B (boundedComparison B (radiusPreimage B γ hγ)) = 0
  rw [comparison_radiusPreimage]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨γ, hγ, rfl⟩)

def comparison (B : Base (M := M)) : Ring B →+* RVDisjointRadiusQuotient.Ring B :=
  Ideal.Quotient.lift _ (comparisonRaw B) (comparison_ideal_zero B)

theorem comparison_mem (B : Base (M := M)) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    comparison B x ∈ RVDisjointRadiusQuotient.piece B n :=
  (IntrinsicBalancedGradings.boundedCoaction B).quotientLift_mem (RVDisjointRadiusQuotient.coaction B)
    (comparisonRaw B) (radiusIdeal B) (ideal_coefficients B) (comparison_ideal_zero B)
    (fun _ _ hy => RVDisjointRadiusQuotient.quotient_mem B (IntrinsicBalancedGradings.boundedComparison_mem B hy)) hx

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_ideal_zero (k : EulerKind) : radiusIdeal B ≤ RingHom.ker (IntrinsicBalancedEvaluations.bounded h00 linear hκ hs B hr hγ hΓ k) := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ', rfl⟩
  exact evaluation_radiusPreimage h00 linear hκ hs B hr hγ hΓ k γ hγ'

def evaluation (k : EulerKind) : Ring B →+* RESDisjointReduction.Ordinary.Ring B :=
  Ideal.Quotient.lift _ (IntrinsicBalancedEvaluations.bounded h00 linear hκ hs B hr hγ hΓ k)
    (evaluation_ideal_zero h00 linear hκ hs B hr hγ hΓ k)

theorem evaluation_mem (k : EulerKind) {n : ℕ} {x : Ring B} (hx : x ∈ piece B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k x ∈ IntrinsicQuotientGradings.OrdinaryRES.piece B n :=
  (IntrinsicBalancedGradings.boundedCoaction B).quotientLift_mem (IntrinsicQuotientGradings.OrdinaryRES.coaction B)
    (IntrinsicBalancedEvaluations.bounded h00 linear hκ hs B hr hγ hΓ k) (radiusIdeal B) (ideal_coefficients B)
    (evaluation_ideal_zero h00 linear hκ hs B hr hγ hΓ k)
    (fun _ _ hy => IntrinsicBalancedEvaluations.bounded_mem h00 linear hκ hs B hr hγ hΓ k hy) hx

theorem evaluation_independent_kind (k l : EulerKind) : evaluation h00 linear hκ hs B hr hγ hΓ k = evaluation h00 linear hκ hs B hr hγ hΓ l := by
  apply Ideal.Quotient.ringHom_ext
  apply DFunLike.ext
  intro x
  exact RingHom.congr_fun (IntrinsicBalancedEvaluations.bounded_independent_kind h00 linear hκ hs B hr hγ hΓ k l) x

theorem evaluation_res (k : EulerKind) (x : RESDisjointPresentation.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (quotient B (x ⊗ₜ[Coeff B] 1)) = IntrinsicBalancedEvaluations.ordinaryLeft B x :=
  IntrinsicBalancedEvaluations.bounded_on_res h00 linear hκ hs B hr hγ hΓ k x

end DiamondIntegral.Section4.IntrinsicBalancedRadiusQuotient
