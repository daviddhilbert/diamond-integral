import «section 4».RESReductionGradings
import «section 4».PositiveIdealDegreeZero

/-! The enlarged measured RES quotient required by the alternative
geometric assignment in Remark 4.8. Actual weighted degree-one point
classes are identified, while degree-zero volume weights are retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAlternativeReduction
open GammaNamesSubgroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pointRelations (B : Base (M := M)) : Set (RESMeasuredReduction.ReducedRing B) :=
  {x | ∃ a : additiveNames B, x = RESMeasuredReduction.pointClass B -
    RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) * RESMeasuredReduction.pointClass B}

def pointIdeal (B : Base (M := M)) : Ideal (RESMeasuredReduction.ReducedRing B) :=
  Ideal.span (pointRelations B)

theorem pointRelations_mem (B : Base (M := M)) (a : additiveNames B) :
    RESMeasuredReduction.pointClass B -
      RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) * RESMeasuredReduction.pointClass B ∈
        RESReductionGradings.measuredPiece B 1 := by
  rw [RESMeasuredReduction.weightCharacter_value]
  apply (RESReductionGradings.measuredPiece B 1).sub_mem (RESReductionGradings.measured_point_mem B)
  simpa only [zero_add] using SetLike.mul_mem_graded
    (RESReductionGradings.measured_weight_mem B _ a.property)
    (RESReductionGradings.measured_point_mem B)

theorem pointIdeal_homogeneous (B : Base (M := M)) :
    (pointIdeal B).IsHomogeneous (RESReductionGradings.measuredPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨a, rfl⟩
  exact ⟨1, pointRelations_mem B a⟩

def Ring (B : Base (M := M)) := RESMeasuredReduction.ReducedRing B ⧸ pointIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESMeasuredReduction.ReducedRing B →+* Ring B :=
  Ideal.Quotient.mk (pointIdeal B)

def fromMeasured (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B :=
  (quotient B).comp (RESMeasuredReduction.quotient B)

theorem ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ pointIdeal B → ((RESReductionGradings.measuredCoaction B).map x).coeff n ∈ pointIdeal B :=
  (RESReductionGradings.measuredCoaction B).homogeneous_ideal_coefficients _ (pointIdeal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RESReductionGradings.measuredCoaction B).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RESMeasuredReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.measuredPiece B n) : quotient B x ∈ piece B n :=
  (RESReductionGradings.measuredCoaction B).quotient_mem _ (ideal_coefficients B) hx

def torusClass (B : Base (M := M)) : Ring B := quotient B (RESMeasuredReduction.torusClass B)
def pointClass (B : Base (M := M)) : Ring B := quotient B (RESMeasuredReduction.pointClass B)
def weightCharacter (B : Base (M := M)) : Multiplicative (additiveNames B) →* Ring B :=
  (quotient B).toMonoidHom.comp (RESMeasuredReduction.weightCharacter B)

theorem weight_mem (B : Base (M := M)) (a : additiveNames B) :
    weightCharacter B (Multiplicative.ofAdd a) ∈ piece B 0 :=
  quotient_mem B (RESReductionGradings.measured_weight_mem B _ a.property)

theorem torus_mem (B : Base (M := M)) : torusClass B ∈ piece B 1 :=
  quotient_mem B (RESReductionGradings.measured_torus_mem B)

theorem point_mem (B : Base (M := M)) : pointClass B ∈ piece B 1 :=
  quotient_mem B (RESReductionGradings.measured_point_mem B)

theorem torus_plus_point_zero (B : Base (M := M)) : torusClass B + pointClass B = 0 := by
  exact (map_add (quotient B) _ _).symm.trans
    ((congrArg (quotient B) (RESMeasuredReduction.torus_plus_point_zero B)).trans (map_zero _))

theorem weighted_point (B : Base (M := M)) (a : additiveNames B) :
    weightCharacter B (Multiplicative.ofAdd a) * pointClass B = pointClass B := by
  have hm : RESMeasuredReduction.pointClass B -
      RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) * RESMeasuredReduction.pointClass B ∈
        pointIdeal B := Ideal.subset_span ⟨a, rfl⟩
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  change quotient B (_ - _) = 0 at h
  rw [map_sub, map_mul] at h
  exact (sub_eq_zero.mp h).symm

theorem weighted_torus (B : Base (M := M)) (a : additiveNames B) :
    weightCharacter B (Multiplicative.ofAdd a) * torusClass B = torusClass B := by
  have hT : torusClass B = -pointClass B := eq_neg_of_add_eq_zero_left (torus_plus_point_zero B)
  rw [hT, mul_neg, weighted_point]

theorem pointIdeal_le_zero_ker (B : Base (M := M)) :
    pointIdeal B ≤ RingHom.ker (RESReductionGradings.measuredCoaction B).zeroProjection := by
  apply Ideal.span_le.mpr
  rintro x ⟨a, rfl⟩
  exact (RESReductionGradings.measuredCoaction B).zeroProjection_of_positive_mem
    (by decide : (1 : ℕ) ≠ 0) (pointRelations_mem B a)

def zeroEquiv (B : Base (M := M)) :
    (RESReductionGradings.measuredCoaction B).zeroSubring ≃+* (coaction B).zeroSubring :=
  (RESReductionGradings.measuredCoaction B).quotientZeroEquiv (pointIdeal B)
    (ideal_coefficients B) (pointIdeal_le_zero_ker B)

end DiamondIntegral.Section4.RESAlternativeReduction
