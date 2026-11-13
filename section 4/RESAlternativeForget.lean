import «section 4».RESAlternativeReduction
import «section 4».RESOrdinaryReduction
import «section 4».CoactionGradedMaps

/-! The alternative enlarged measured RES quotient maps, by forgetting
volume, to the actual ordinary RES fibre quotient modulo the affine line.
Both quotients and the map retain their full gradings. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAlternativeForget
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def affineClass (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B :=
  RESOrdinaryReduction.torusClass B + RESOrdinaryReduction.pointClass B

def affineIdeal (B : Base (M := M)) : Ideal (RESOrdinaryReduction.ReducedRing B) :=
  Ideal.span {affineClass B}

theorem affine_mem (B : Base (M := M)) : affineClass B ∈ RESReductionGradings.ordinaryPiece B 1 :=
  (RESReductionGradings.ordinaryPiece B 1).add_mem
    (RESReductionGradings.ordinary_class_mem B _) (RESReductionGradings.ordinary_class_mem B _)

theorem affineIdeal_homogeneous (B : Base (M := M)) :
    (affineIdeal B).IsHomogeneous (RESReductionGradings.ordinaryPiece B) := by
  apply Ideal.homogeneous_span
  intro x hx
  have he : x = affineClass B := hx
  subst x
  exact ⟨1, affine_mem B⟩

def Ring (B : Base (M := M)) := RESOrdinaryReduction.ReducedRing B ⧸ affineIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B →+* Ring B :=
  Ideal.Quotient.mk (affineIdeal B)

theorem affine_zero (B : Base (M := M)) : quotient B (affineClass B) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem ideal_coefficients (B : Base (M := M)) :
    ∀ n x, x ∈ affineIdeal B → ((RESReductionGradings.ordinaryCoaction B).map x).coeff n ∈ affineIdeal B :=
  (RESReductionGradings.ordinaryCoaction B).homogeneous_ideal_coefficients _ (affineIdeal_homogeneous B)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Ring B) :=
  (RESReductionGradings.ordinaryCoaction B).quotient _ (ideal_coefficients B)

def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Ring B) := (coaction B).piece n

instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem quotient_mem (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) : quotient B x ∈ piece B n :=
  (RESReductionGradings.ordinaryCoaction B).quotient_mem _ (ideal_coefficients B) hx

def rawForget (B : Base (M := M)) : RESChartRing.Ring B →+* Ring B :=
  (quotient B).comp (RESOrdinaryReduction.forget B)

theorem rawForget_affine (B : Base (M := M)) : rawForget B (RESMeasuredReduction.affineClass B) = 0 := by
  change quotient B (RESOrdinaryReduction.forget B
    (RESChartRing.objectClass (RESFibreObjects.torus B) + RESChartRing.objectClass (RESFibreObjects.point B))) = 0
  rw [map_add, RESOrdinaryReduction.forget_objectClass, RESOrdinaryReduction.forget_objectClass]
  exact affine_zero B

theorem reductionIdeal_le_ker (B : Base (M := M)) :
    RESMeasuredReduction.reductionIdeal B ≤ RingHom.ker (rawForget B) := by
  apply sup_le
  · intro x hx
    change quotient B (RESOrdinaryReduction.forget B x) = 0
    rw [RESOrdinaryReduction.forget_kills_measuredFibreIdeal B hx, map_zero]
  · apply Ideal.span_le.mpr
    intro x hx
    have he : x = RESMeasuredReduction.affineClass B := hx
    subst x
    exact rawForget_affine B

def measuredForget (B : Base (M := M)) : RESMeasuredReduction.ReducedRing B →+* Ring B :=
  Ideal.Quotient.lift _ (rawForget B) (reductionIdeal_le_ker B)

theorem measuredForget_point (B : Base (M := M)) :
    measuredForget B (RESMeasuredReduction.pointClass B) = quotient B (RESOrdinaryReduction.pointClass B) := by
  change quotient B (RESOrdinaryReduction.forget B (RESChartRing.objectClass (RESFibreObjects.point B))) = _
  rw [RESOrdinaryReduction.forget_objectClass]
  rfl

theorem measuredForget_torus (B : Base (M := M)) :
    measuredForget B (RESMeasuredReduction.torusClass B) = quotient B (RESOrdinaryReduction.torusClass B) := by
  change quotient B (RESOrdinaryReduction.forget B (RESChartRing.objectClass (RESFibreObjects.torus B))) = _
  rw [RESOrdinaryReduction.forget_objectClass]
  rfl

theorem measuredForget_weight (B : Base (M := M)) (a : GammaNamesSubgroup.additiveNames B) :
    measuredForget B (RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a)) = 1 := by
  change quotient B (RESOrdinaryReduction.forget B
    (RESChartRing.objectClass (RVMeasuredCharts.weightedRESUnit B
      (GammaDefinableEuler.toPaperGamma.symm a.val) a.property))) = 1
  exact (congrArg (quotient B) (RESOrdinaryReduction.forget_weightedUnit B
    (GammaDefinableEuler.toPaperGamma.symm a.val) a.property)).trans (map_one _)

theorem pointIdeal_le_ker (B : Base (M := M)) :
    RESAlternativeReduction.pointIdeal B ≤ RingHom.ker (measuredForget B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨a, rfl⟩
  change measuredForget B (_ - _) = 0
  rw [map_sub, map_mul, measuredForget_point, measuredForget_weight, one_mul, sub_self]

def forget (B : Base (M := M)) : RESAlternativeReduction.Ring B →+* Ring B :=
  Ideal.Quotient.lift _ (measuredForget B) (pointIdeal_le_ker B)

theorem forget_fromMeasured (B : Base (M := M)) (x : RESChartRing.Ring B) :
    forget B (RESAlternativeReduction.fromMeasured B x) = rawForget B x := rfl

theorem measuredForget_mem (B : Base (M := M)) {n : ℕ} {x : RESMeasuredReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.measuredPiece B n) : measuredForget B x ∈ piece B n :=
  (RESGrading.gradingCoaction B).quotientLift_mem (coaction B) (rawForget B)
    (RESMeasuredReduction.reductionIdeal B) (RESReductionGradings.measured_ideal_coefficients B)
    (reductionIdeal_le_ker B) (fun _ _ hx => quotient_mem B (RESReductionGradings.forget_mem B hx)) hx

theorem forget_mem (B : Base (M := M)) {n : ℕ} {x : RESAlternativeReduction.Ring B}
    (hx : x ∈ RESAlternativeReduction.piece B n) : forget B x ∈ piece B n :=
  (RESReductionGradings.measuredCoaction B).quotientLift_mem (coaction B) (measuredForget B)
    (RESAlternativeReduction.pointIdeal B) (RESAlternativeReduction.ideal_coefficients B)
    (pointIdeal_le_ker B) (fun _ _ hx => measuredForget_mem B hx) hx

def gradedForget (B : Base (M := M)) : GradedRingHom (RESAlternativeReduction.piece B) (piece B) where
  toRingHom := forget B
  map_mem := fun hx => forget_mem B hx

end DiamondIntegral.Section4.RESAlternativeForget
