import «section 4».RVBalancedRadiusIdeal
import «section 4».CoactionGradedMaps

/-! Actual graded comparison and ordinary RES evaluation on the bounded
finite-Gamma-balanced tensor modulo the accepted radius relations. This
quotient does not assert descent through the full RV comparison kernel. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBalancedRadiusQuotient
open RVBalancedGradings RVBalancedRadiusIdeal
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def Ring (B : Base (M := M)) := RVBoundedBalancedTensor.Source B ⧸ radiusIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVBoundedBalancedTensor.Source B →+* Ring B :=
  Ideal.Quotient.mk (radiusIdeal B)

theorem ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ radiusIdeal B → ((boundedCoaction B).map x).coeff n ∈ radiusIdeal B :=
  (boundedCoaction B).homogeneous_ideal_coefficients _ (radiusIdeal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (boundedCoaction B).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RVBoundedBalancedTensor.Source B}
    (hx : x ∈ boundedPiece B n) : quotient B x ∈ piece B n :=
  (boundedCoaction B).quotient_mem _ (ideal_coefficients B) hx

theorem radiusPreimage_zero (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ GammaRVLifts.admissibleRadii B) :
    quotient B (RVBalancedSpecialClasses.radiusPreimage B γ hγ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (radiusPreimage_mem_ideal B γ hγ)

theorem radiusIdeal_le_comparison_ker (B : Base (M := M)) :
    radiusIdeal B ≤ RingHom.ker ((RVRadiusQuotient.quotient B).comp (RVBoundedBalancedTensor.comparison B).toRingHom) := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  change RVRadiusQuotient.quotient B (RVBoundedBalancedTensor.comparison B
    (RVBalancedSpecialClasses.radiusPreimage B γ hγ)) = 0
  rw [RVBalancedSpecialClasses.comparison_radiusPreimage]
  exact RVRadiusQuotient.pGamma_zero B γ hγ

def comparison (B : Base (M := M)) : GradedRingHom (piece B) (RVRadiusQuotient.piece B) :=
  (boundedCoaction B).gradedQuotientLift (RVRadiusQuotient.coaction B)
    ((RVRadiusQuotient.quotient B).comp (RVBoundedBalancedTensor.comparison B).toRingHom)
    (radiusIdeal B) (ideal_coefficients B) (fun x hx => radiusIdeal_le_comparison_ker B hx)
    (fun _ _ hx => RVRadiusQuotient.quotient_mem B ((RVBalancedMapGradings.gradedBoundedComparison B).map_mem hx))

theorem comparison_mk (B : Base (M := M)) (x : RVBoundedBalancedTensor.Source B) :
    comparison B (quotient B x) = RVRadiusQuotient.quotient B (RVBoundedBalancedTensor.comparison B x) := rfl

def evaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (piece B) (RESReductionGradings.ordinaryPiece B) :=
  (boundedCoaction B).gradedQuotientLift (RESReductionGradings.ordinaryCoaction B)
    (RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom
    (radiusIdeal B) (ideal_coefficients B)
    (fun x hx => radiusIdeal_le_evaluation_ker hc h00 linear hκ hs B hr hγ hΓ k hx)
    (fun _ _ hx => (RVBalancedMapGradings.gradedBoundedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).map_mem hx)

theorem evaluation_mk (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RVBoundedBalancedTensor.Source B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (quotient B x) =
      RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k x := rfl

def ofRES (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B :=
  (quotient B).comp (RVBoundedBalancedTensor.resInclusion B).toRingHom

theorem ofRES_mem (B : Base (M := M)) {n : ℕ} {x : RESChartRing.Ring B}
    (hx : x ∈ RESRingCoaction.gradedPiece B n) : ofRES B x ∈ piece B n :=
  quotient_mem B (RVBalancedGradings.bounded_tmul_mem B hx (SetLike.one_mem_graded _))

theorem comparison_ofRES (B : Base (M := M)) (x : RESChartRing.Ring B) :
    comparison B (ofRES B x) = RVRadiusQuotient.ofRES B x :=
  congrArg (RVRadiusQuotient.quotient B) (RVBoundedBalancedTensor.comparison_res B x)

theorem evaluation_ofRES (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    evaluation hc h00 linear hκ hs B hr hγ hΓ k (ofRES B x) = RESOrdinaryReduction.forget B x :=
  RVBoundedBalancedTensor.evaluation_res hc h00 linear hκ hs B hr hγ hΓ k x

theorem evaluation_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    (evaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom =
      (evaluation hc h00 linear hκ hs B hr hγ hΓ l).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (RVBoundedBalancedTensor.evaluation_independent_kind hc h00 linear hκ hs B hr hγ hΓ k l) x

end DiamondIntegral.Section4.RVBalancedRadiusQuotient
