import «section 4».RESMeasuredReduction
import «section 4».GammaUnboundedAssignments

/-! The unbounded polynomial-source homomorphism now has a concrete
measured RES chart quotient as target. The point/ray/line assignments and
the counterweighted-ray values use actual weighted torus and point
objects. This does not construct the RV tensor descent or a grading. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESUnboundedPsi
open RESMeasuredReduction GammaNamesSubgroup GammaDefinableEuler GammaUnboundedSpecialization
open GammaUnboundedAssignments GammaCounterweightedRay GammaObjectPolynomial

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def weightedTorus (B : Base (M := M)) (a : additiveNames B) : ReducedRing B :=
  quotient B (RESChartRing.objectClass (RVWeightScaling.scaledRES (RESFibreObjects.torus B)
    (toPaperGamma.symm a.val) a.property))

def weightedPoint (B : Base (M := M)) (a : additiveNames B) : ReducedRing B :=
  quotient B (RESChartRing.objectClass (RVWeightScaling.scaledRES (RESFibreObjects.point B)
    (toPaperGamma.symm a.val) a.property))

theorem weightedTorus_formula (B : Base (M := M)) (a : additiveNames B) :
    weightedTorus B a = RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) * torusClass B :=
  scaled_class B (RESFibreObjects.torus B) (toPaperGamma.symm a.val) a.property

theorem weightedPoint_formula (B : Base (M := M)) (a : additiveNames B) :
    weightedPoint B a = RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) * pointClass B :=
  scaled_class B (RESFibreObjects.point B) (toPaperGamma.symm a.val) a.property

def psi (B : Base (M := M)) (k : EulerKind) : GammaFunctionPolynomial.sourceRing B k →+* ReducedRing B :=
  specialize B k (RESMeasuredReduction.weightCharacter B) (torusClass B)

theorem psi_point_positive (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    psi B k (pointMonomial B k n a) = (torusClass B) ^ (n - 1) * weightedTorus B a := by
  have h := specialize_point_positive B k (RESMeasuredReduction.weightCharacter B) (torusClass B) n hn a
  exact h.trans (congrArg ((torusClass B) ^ (n - 1) * ·) (weightedTorus_formula B a).symm)

theorem psi_ray_positive (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) (a : additiveNames B) :
    psi B k (rayMonomial B k n hn a) = (torusClass B) ^ (n - 1) * weightedPoint B a := by
  have h := specialize_ray_pointClass B k (RESMeasuredReduction.weightCharacter B) (torusClass B) (pointClass B)
    (point_plus_torus_zero B) n hn a
  exact h.trans (congrArg ((torusClass B) ^ (n - 1) * ·) (weightedPoint_formula B a).symm)

theorem psi_line_positive (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) :
    psi B k (lineMonomial B k n hn) = 0 :=
  specialize_line B k (RESMeasuredReduction.weightCharacter B) (torusClass B) n hn

theorem psi_point_zero (B : Base (M := M)) (k : EulerKind) (a : additiveNames B) :
    psi B k (pointMonomial B k 0 a) =
      RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) := by
  unfold psi
  have h := specialize_point B k (RESMeasuredReduction.weightCharacter B) (torusClass B) 0 a
  simpa only [pow_zero, mul_one] using h

theorem psi_counterweighted_geometric (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    psi B EulerKind.geometric
      (objectPolynomial h00 hκ hs B hr hγ EulerKind.geometric 1 positiveRay (positiveRay_definable B)
        inverseCoordinate (inverseCoordinate_definable B)) = pointClass B :=
  specialize_counterweighted_geometric h00 hκ hs B hr hγ (RESMeasuredReduction.weightCharacter B)
    (torusClass B) (pointClass B) (point_plus_torus_zero B)

theorem psi_counterweighted_bounded (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    psi B EulerKind.bounded
      (objectPolynomial h00 hκ hs B hr hγ EulerKind.bounded 1 positiveRay (positiveRay_definable B)
        inverseCoordinate (inverseCoordinate_definable B)) = 0 :=
  specialize_counterweighted_bounded h00 hκ hs B hr hγ (RESMeasuredReduction.weightCharacter B) (torusClass B)

end DiamondIntegral.Section4.RESUnboundedPsi
