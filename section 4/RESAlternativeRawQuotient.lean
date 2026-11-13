import «section 4».RESAlternativeReduction
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The enlarged target is exactly the raw measured RES quotient by the
original fibre and affine relations together with the actual weighted
point differences stated in Remark 4.8. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAlternativeRawQuotient
open GammaNamesSubgroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rawPointDifference (B : Base (M := M)) (a : additiveNames B) : RESChartRing.Ring B :=
  RESChartRing.objectClass (RESFibreObjects.point B) -
    RESChartRing.objectClass (RVWeightScaling.scaledRES (RESFibreObjects.point B)
      (GammaDefinableEuler.toPaperGamma.symm a.val) a.property)

def rawPointIdeal (B : Base (M := M)) : Ideal (RESChartRing.Ring B) :=
  Ideal.span (Set.range (rawPointDifference B))

theorem pointDifference_map (B : Base (M := M)) (a : additiveNames B) :
    RESMeasuredReduction.quotient B (rawPointDifference B a) =
      RESMeasuredReduction.pointClass B -
        RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd a) * RESMeasuredReduction.pointClass B := by
  rw [rawPointDifference, map_sub]
  exact congrArg (fun x => RESMeasuredReduction.pointClass B - x)
    (RESMeasuredReduction.scaled_class B (RESFibreObjects.point B)
      (GammaDefinableEuler.toPaperGamma.symm a.val) a.property)

theorem pointIdeal_map (B : Base (M := M)) :
    Ideal.map (RESMeasuredReduction.quotient B) (rawPointIdeal B) = RESAlternativeReduction.pointIdeal B := by
  rw [rawPointIdeal, Ideal.map_span, RESAlternativeReduction.pointIdeal]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, pointDifference_map B a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨rawPointDifference B a, Set.mem_range_self a, pointDifference_map B a⟩

def rawIdeal (B : Base (M := M)) : Ideal (RESChartRing.Ring B) :=
  RESMeasuredReduction.reductionIdeal B ⊔ rawPointIdeal B

def RawRing (B : Base (M := M)) := RESChartRing.Ring B ⧸ rawIdeal B
  deriving CommRing

def equivalence (B : Base (M := M)) : RESAlternativeReduction.Ring B ≃+* RawRing B :=
  (Ideal.quotEquivOfEq (pointIdeal_map B).symm).trans
    (DoubleQuot.quotQuotEquivQuotSup (RESMeasuredReduction.reductionIdeal B) (rawPointIdeal B))

theorem equivalence_fromMeasured (B : Base (M := M)) (x : RESChartRing.Ring B) :
    equivalence B (RESAlternativeReduction.fromMeasured B x) = Ideal.Quotient.mk (rawIdeal B) x := rfl

theorem kernel_fromMeasured (B : Base (M := M)) :
    RingHom.ker (RESAlternativeReduction.fromMeasured B) = rawIdeal B := by
  ext x
  change RESAlternativeReduction.fromMeasured B x = 0 ↔ x ∈ rawIdeal B
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have he := congrArg (equivalence B) h
    rwa [equivalence_fromMeasured, map_zero] at he
  · intro h
    apply (equivalence B).injective
    rw [equivalence_fromMeasured, map_zero]
    exact h

end DiamondIntegral.Section4.RESAlternativeRawQuotient
