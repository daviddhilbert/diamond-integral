import «section 4».RESOrdinaryRing
import «section 4».RESMeasuredReduction

/-! The concrete ordinary RES quotient by value-fibre minus torus
relations. The actual measured-to-ordinary forgetful map kills the
measured fibre ideal and all zero-degree volume weights. The affine-line
class is not killed in this bounded target. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESOrdinaryReduction
open RVMeasuredCharts RESFibreObjects

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fibreRelations (B : Base (M := M)) : Set (RESOrdinaryRing.Ring B) :=
  {x | ∃ α : Values.Gamma (M := M), ∃ hα : GammaDefinableClosureAtBase B α,
    x = RESOrdinaryRing.objectClass (fibre B α 1 hα (GammaGroupNames.one_definable_base B)) -
      RESOrdinaryRing.objectClass (torus B)}

def fibreIdeal (B : Base (M := M)) : Ideal (RESOrdinaryRing.Ring B) := Ideal.span (fibreRelations B)

def ReducedRing (B : Base (M := M)) := RESOrdinaryRing.Ring B ⧸ fibreIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RESOrdinaryRing.Ring B →+* ReducedRing B := Ideal.Quotient.mk (fibreIdeal B)

def torusClass (B : Base (M := M)) : ReducedRing B := quotient B (RESOrdinaryRing.objectClass (torus B))

def pointClass (B : Base (M := M)) : ReducedRing B := quotient B (RESOrdinaryRing.objectClass (point B))

def forget (B : Base (M := M)) : RESChartRing.Ring B →+* ReducedRing B := (quotient B).comp (RESOrdinaryRing.forget B)

theorem forget_objectClass (B : Base (M := M)) {k : ℕ} (a : RESChart B k) :
    forget B (RESChartRing.objectClass a) = quotient B (RESOrdinaryRing.objectClass a) :=
  congrArg (quotient B) (RESOrdinaryRing.forget_objectClass B a)

theorem forget_weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : forget B (RESChartRing.objectClass (weightedRESUnit B γ hγ)) = 1 := by
  change quotient B (RESOrdinaryRing.forget B (RESChartRing.objectClass (weightedRESUnit B γ hγ))) = 1
  rw [RESOrdinaryRing.forget_weightedUnit, map_one]

theorem forget_scaled (B : Base (M := M)) {k : ℕ} (a : RESChart B k) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) :
    forget B (RESChartRing.objectClass (RVWeightScaling.scaledRES a γ hγ)) = forget B (RESChartRing.objectClass a) :=
  (forget_objectClass B _).trans ((congrArg (quotient B) (RESOrdinaryRing.scaled_class a γ hγ)).trans
    (forget_objectClass B a).symm)

theorem fibre_class (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    quotient B (RESOrdinaryRing.objectClass (fibre B α β hα hβ)) = torusClass B := by
  have he : RESOrdinaryRing.objectClass (fibre B α β hα hβ) =
      RESOrdinaryRing.objectClass (fibre B α 1 hα (GammaGroupNames.one_definable_base B)) :=
    (RESOrdinaryRing.objectClass_trivial (fibre B α β hα hβ)).trans
      (RESOrdinaryRing.objectClass_trivial (fibre B α 1 hα (GammaGroupNames.one_definable_base B))).symm
  have hmem : RESOrdinaryRing.objectClass (fibre B α 1 hα (GammaGroupNames.one_definable_base B)) -
      RESOrdinaryRing.objectClass (torus B) ∈ fibreIdeal B := Ideal.subset_span ⟨α, hα, rfl⟩
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  change quotient B (_ - _) = 0 at h
  rw [map_sub] at h
  exact (congrArg (quotient B) he).trans (sub_eq_zero.mp h)

theorem forget_fibre (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    forget B (RESChartRing.objectClass (fibre B α β hα hβ)) = torusClass B :=
  (forget_objectClass B _).trans (fibre_class B α β hα hβ)

theorem forget_kills_measuredFibreIdeal (B : Base (M := M)) :
    RESMeasuredReduction.fibreIdeal B ≤ RingHom.ker (forget B) := by
  apply Ideal.span_le.mpr
  rintro r ⟨α, β, hα, hβ, rfl⟩
  change forget B (_ - _) = 0
  rw [map_sub, forget_scaled, forget_fibre, forget_objectClass]
  exact sub_self _

def forgetFibreQuotient (B : Base (M := M)) :
    (RESChartRing.Ring B ⧸ RESMeasuredReduction.fibreIdeal B) →+* ReducedRing B :=
  Ideal.Quotient.lift (RESMeasuredReduction.fibreIdeal B) (forget B)
    (fun _ hr => forget_kills_measuredFibreIdeal B hr)

end DiamondIntegral.Section4.RESOrdinaryReduction
