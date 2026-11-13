import «section 4».RESFibreObjects
import «section 4».RVWeightScaling

/-! The concrete measured RES chart quotient by the actual value-fibre
relations and the homogeneous affine-line class. The torus, degree-one
point and degree-zero weight character are realized by actual objects.
Grading/category identification and RV tensor descent remain open. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESMeasuredReduction
open RVMeasuredCharts RESFibreObjects RVWeightScaling

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fibreRelations (B : Base (M := M)) : Set (RESChartRing.Ring B) :=
  {x | ∃ α β : Values.Gamma (M := M), ∃ hα : GammaDefinableClosureAtBase B α,
    ∃ hβ : GammaDefinableClosureAtBase B β,
    x = RESChartRing.objectClass (scaledRES (torus B) (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ)) -
      RESChartRing.objectClass (fibre B α β hα hβ)}

def fibreIdeal (B : Base (M := M)) : Ideal (RESChartRing.Ring B) := Ideal.span (fibreRelations B)

def affineClass (B : Base (M := M)) : RESChartRing.Ring B :=
  RESChartRing.objectClass (torus B) + RESChartRing.objectClass (point B)

def reductionIdeal (B : Base (M := M)) : Ideal (RESChartRing.Ring B) :=
  fibreIdeal B ⊔ Ideal.span {affineClass B}

def ReducedRing (B : Base (M := M)) := RESChartRing.Ring B ⧸ reductionIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESChartRing.Ring B →+* ReducedRing B := Ideal.Quotient.mk (reductionIdeal B)

def torusClass (B : Base (M := M)) : ReducedRing B := quotient B (RESChartRing.objectClass (torus B))

def pointClass (B : Base (M := M)) : ReducedRing B := quotient B (RESChartRing.objectClass (point B))

def weightValue (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : ReducedRing B :=
  quotient B (RESChartRing.objectClass (weightedRESUnit B γ hγ))

def weightCharacter (B : Base (M := M)) : Multiplicative (GammaNamesSubgroup.additiveNames B) →* ReducedRing B :=
  (quotient B).toMonoidHom.comp (RESWeightCharacter.weightCharacter B)

theorem weightCharacter_value (B : Base (M := M)) (a : GammaNamesSubgroup.additiveNames B) :
    weightCharacter B (Multiplicative.ofAdd a) = weightValue B (GammaDefinableEuler.toPaperGamma.symm a.val) a.property := rfl

theorem torus_plus_point_zero (B : Base (M := M)) : torusClass B + pointClass B = 0 := by
  have hmem : affineClass B ∈ reductionIdeal B := by
    have hincl : Ideal.span {affineClass B} ≤ reductionIdeal B := le_sup_right
    exact hincl (Ideal.subset_span (Set.mem_singleton _))
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  change quotient B (affineClass B) = 0 at h
  change quotient B (RESChartRing.objectClass (torus B) + RESChartRing.objectClass (point B)) = 0 at h
  rw [map_add] at h
  exact h

theorem point_plus_torus_zero (B : Base (M := M)) : pointClass B + torusClass B = 0 := by
  rw [add_comm]
  exact torus_plus_point_zero B

theorem scaled_class (B : Base (M := M)) {k : ℕ} (a : RESChart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) :
    quotient B (RESChartRing.objectClass (scaledRES a γ hγ)) = weightValue B γ hγ * quotient B (RESChartRing.objectClass a) :=
  (congrArg (quotient B) (scaledRES_class a γ hγ)).trans (map_mul (quotient B) _ _)

theorem fibre_class_eq_scaled (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    quotient B (RESChartRing.objectClass (fibre B α β hα hβ)) =
      quotient B (RESChartRing.objectClass
        (scaledRES (torus B) (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ))) := by
  have hmem : RESChartRing.objectClass
      (scaledRES (torus B) (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ)) -
      RESChartRing.objectClass (fibre B α β hα hβ) ∈ reductionIdeal B := by
    have hincl : fibreIdeal B ≤ reductionIdeal B := le_sup_left
    exact hincl (Ideal.subset_span ⟨α, β, hα, hβ, rfl⟩)
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  change quotient B (_ - _) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem fibre_class (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    quotient B (RESChartRing.objectClass (fibre B α β hα hβ)) =
      weightValue B (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ) * torusClass B :=
  (fibre_class_eq_scaled B α β hα hβ).trans
    (scaled_class B (torus B) (α * β) (GammaGroupNames.mul_definable_base B α β hα hβ))

end DiamondIntegral.Section4.RESMeasuredReduction
