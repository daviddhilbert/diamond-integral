import «section 4».RVFiniteWeightedCounts
import «section 4».RVChartMaps
import «section 4».RVBoundedMaps

/-! A genuine ring-valued weighted count on degree-zero actual RV
objects, extended by zero on positive grades. It retains every Gamma
volume value and uses finite cardinality without definable point choices. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVZeroWeightedCount
open RVMeasuredCharts RVFiniteWeightedCounts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def value (B : Base (M := M)) : ∀ k, Chart B k → Target M
  | 0, a => count a a.zero_domain_finite
  | _ + 1, _ => 0

def invariant (B : Base (M := M)) : RVChartRing.Invariant B (Target M) where
  value := value B
  unit := by
    change count (weightedUnit B 1 (GammaGroupNames.one_definable_base B)) _ = 1
    rw [count_weightedUnit, ← MonoidAlgebra.one_def]
  product k l a b := by
    cases k <;> cases l
    · exact count_product a b a.zero_domain_finite b.zero_domain_finite
    · exact (mul_zero _).symm
    · exact (zero_mul _).symm
    · exact (zero_mul _).symm
  iso k a b F := by
    cases k
    · exact count_iso a.zero_domain_finite b.zero_domain_finite F
    · rfl
  empty k a ha := by
    cases k
    · exact count_empty a a.zero_domain_finite ha
    · rfl
  scissor k a b c d h := by
    cases k
    · exact count_scissor a b c d a.zero_domain_finite b.zero_domain_finite c.zero_domain_finite d.zero_domain_finite h
    · rfl

def full (B : Base (M := M)) : RVChartRing.Ring B →+* Target M := RVChartRing.lift B (invariant B)

theorem full_class (B : Base (M := M)) {k : ℕ} (a : Chart B k) :
    full B (RVChartRing.objectClass a) = value B k a := RVChartRing.lift_objectClass B (invariant B) a

def res (B : Base (M := M)) : RESChartRing.Ring B →+* Target M := (full B).comp (RVChartMaps.ofRES B)

theorem res_weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) :
    res B (RESChartRing.objectClass (weightedRESUnit B γ hγ)) = MonoidAlgebra.single γ 1 := by
  change full B (RVChartMaps.ofRES B (RESChartRing.objectClass (weightedRESUnit B γ hγ))) = _
  rw [RVChartMaps.ofRES_class, full_class]
  exact count_weightedUnit B γ hγ

def bounded (B : Base (M := M)) : RVBoundedRing.Ring B →+* Target M :=
  (full B).comp (RVBoundedMaps.forget B)

theorem bounded_ofRES (B : Base (M := M)) : (bounded B).comp (RVBoundedMaps.ofRES B) = res B := by
  change (full B).comp ((RVBoundedMaps.forget B).comp (RVBoundedMaps.ofRES B)) = _
  rw [RVBoundedMaps.forget_ofRES]
  rfl

end DiamondIntegral.Section4.RVZeroWeightedCount
