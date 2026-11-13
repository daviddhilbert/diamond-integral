import «section 4».RESDisjointGrading
import «section 4».RESOrdinaryDisjointGrading
import «section 4».RESReductionGradings
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Actual value-fibre reductions in the intrinsic RES presentations.
The measured target also kills the homogeneous affine line; the ordinary
fibre reduction retains it. Their specified generator ideals map exactly
to the corresponding scissor-presentation ideals. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESDisjointReduction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

namespace Measured
open RESDisjointPresentation RESFibreObjects RVWeightScaling

def fibreRelations (B : Base (M := M)) : Set (RESDisjointPresentation.Ring B) :=
  {x | ∃ α β : Values.Gamma (M := M), ∃ hα : GammaDefinableClosureAtBase B α,
    ∃ hβ : GammaDefinableClosureAtBase B β,
    x = objectClass (scaledRES (torus B) (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ)) -
      objectClass (fibre B α β hα hβ)}

def fibreIdeal (B : Base (M := M)) : Ideal (RESDisjointPresentation.Ring B) := Ideal.span (fibreRelations B)

def affineClass (B : Base (M := M)) : RESDisjointPresentation.Ring B := objectClass (torus B) + objectClass (point B)

def reductionIdeal (B : Base (M := M)) : Ideal (RESDisjointPresentation.Ring B) := fibreIdeal B ⊔ Ideal.span {affineClass B}

theorem image_fibreRelations (B : Base (M := M)) :
    toChartRing B '' fibreRelations B = RESMeasuredReduction.fibreRelations B := by
  ext x
  constructor
  · rintro ⟨y, ⟨α, β, hα, hβ, rfl⟩, rfl⟩
    refine ⟨α, β, hα, hβ, ?_⟩
    rw [map_sub, toChartRing_class, toChartRing_class]
  · rintro ⟨α, β, hα, hβ, rfl⟩
    refine ⟨objectClass (scaledRES (torus B) (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ)) -
      objectClass (fibre B α β hα hβ), ⟨α, β, hα, hβ, rfl⟩, ?_⟩
    rw [map_sub, toChartRing_class, toChartRing_class]

theorem map_fibreIdeal (B : Base (M := M)) :
    (fibreIdeal B).map (toChartRing B) = RESMeasuredReduction.fibreIdeal B := by
  rw [fibreIdeal, RESMeasuredReduction.fibreIdeal, Ideal.map_span, image_fibreRelations]

theorem toChart_affineClass (B : Base (M := M)) : toChartRing B (affineClass B) = RESMeasuredReduction.affineClass B := by
  rw [affineClass, RESMeasuredReduction.affineClass, map_add, toChartRing_class, toChartRing_class]

theorem map_reductionIdeal (B : Base (M := M)) :
    (reductionIdeal B).map (toChartRing B) = RESMeasuredReduction.reductionIdeal B := by
  rw [reductionIdeal, RESMeasuredReduction.reductionIdeal, Ideal.map_sup, map_fibreIdeal,
    Ideal.map_span, Set.image_singleton, toChart_affineClass]

def Ring (B : Base (M := M)) := RESDisjointPresentation.Ring B ⧸ reductionIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESDisjointPresentation.Ring B →+* Ring B := Ideal.Quotient.mk _

def equivalence (B : Base (M := M)) : Ring B ≃+* RESMeasuredReduction.ReducedRing B :=
  Ideal.quotientEquiv (reductionIdeal B) (RESMeasuredReduction.reductionIdeal B)
    (RESDisjointPresentation.equivalence B) (map_reductionIdeal B).symm

theorem equivalence_quotient (B : Base (M := M)) (x : RESDisjointPresentation.Ring B) :
    equivalence B (quotient B x) = RESMeasuredReduction.quotient B (toChartRing B x) := rfl

theorem equivalence_class (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    equivalence B (quotient B (objectClass a)) = RESMeasuredReduction.quotient B (RESChartRing.objectClass a) := by
  rw [equivalence_quotient, toChartRing_class]

end Measured

namespace Ordinary
open RESOrdinaryDisjointPresentation RESFibreObjects

def fibreRelations (B : Base (M := M)) : Set (RESOrdinaryDisjointPresentation.Ring B) :=
  {x | ∃ α : Values.Gamma (M := M), ∃ hα : GammaDefinableClosureAtBase B α,
    x = objectClass (fibre B α 1 hα (GammaGroupNames.one_definable_base B)) - objectClass (torus B)}

def fibreIdeal (B : Base (M := M)) : Ideal (RESOrdinaryDisjointPresentation.Ring B) := Ideal.span (fibreRelations B)

theorem image_fibreRelations (B : Base (M := M)) :
    toChartRing B '' fibreRelations B = RESOrdinaryReduction.fibreRelations B := by
  ext x
  constructor
  · rintro ⟨y, ⟨α, hα, rfl⟩, rfl⟩
    refine ⟨α, hα, ?_⟩
    rw [map_sub, toChartRing_class, toChartRing_class]
  · rintro ⟨α, hα, rfl⟩
    refine ⟨objectClass (fibre B α 1 hα (GammaGroupNames.one_definable_base B)) - objectClass (torus B),
      ⟨α, hα, rfl⟩, ?_⟩
    rw [map_sub, toChartRing_class, toChartRing_class]

theorem map_fibreIdeal (B : Base (M := M)) :
    (fibreIdeal B).map (toChartRing B) = RESOrdinaryReduction.fibreIdeal B := by
  rw [fibreIdeal, RESOrdinaryReduction.fibreIdeal, Ideal.map_span, image_fibreRelations]

def Ring (B : Base (M := M)) := RESOrdinaryDisjointPresentation.Ring B ⧸ fibreIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESOrdinaryDisjointPresentation.Ring B →+* Ring B := Ideal.Quotient.mk _

def equivalence (B : Base (M := M)) : Ring B ≃+* RESOrdinaryReduction.ReducedRing B :=
  Ideal.quotientEquiv (fibreIdeal B) (RESOrdinaryReduction.fibreIdeal B)
    (RESOrdinaryDisjointPresentation.equivalence B) (map_fibreIdeal B).symm

theorem equivalence_quotient (B : Base (M := M)) (x : RESOrdinaryDisjointPresentation.Ring B) :
    equivalence B (quotient B x) = RESOrdinaryReduction.quotient B (toChartRing B x) := rfl

theorem equivalence_class (B : Base (M := M)) {k : ℕ} (a : RVMeasuredCharts.RESChart B k) :
    equivalence B (quotient B (objectClass a)) = RESOrdinaryReduction.quotient B (RESOrdinaryRing.objectClass a) := by
  rw [equivalence_quotient, toChartRing_class]

end Ordinary
end DiamondIntegral.Section4.RESDisjointReduction
