import «section 4».RVChartDisjointUnion
import «section 4».RVBoundedRing
import «section 4».RESOrdinaryRing
import «section 4».RVOrdinaryRing

/-! Common-arity disjoint unions preserve actual finite RES value patterns
and bounded RV domains. Their class is the sum in each concrete measured
or ordinary ring. No category identification is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVChartUnionProperties
open RVMeasuredCharts RVChartDisjointUnion RVMeasuredBounds
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem finite_patterns {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : Disjoint a.domain b.domain) (ha : (Set.range a.toChart.valuePattern).Finite)
    (hb : (Set.range b.toChart.valuePattern).Finite) :
    (Set.range (disjointUnion a b hd).toChart.valuePattern).Finite := by
  apply (ha.union hb).subset
  rintro p ⟨u, rfl⟩
  rcases u.property with hua | hub
  · exact Or.inl ⟨⟨u.val, hua⟩, rfl⟩
  · exact Or.inr ⟨⟨u.val, hub⟩, rfl⟩

def resUnion {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain)
    (ha : (Set.range a.toChart.valuePattern).Finite) (hb : (Set.range b.toChart.valuePattern).Finite) : RESChart B k :=
  ⟨(disjointUnion a b hd).toChart, finite_patterns a b hd ha hb⟩

theorem domain_bounded {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : Disjoint a.domain b.domain) (ha : DomainBounded a.toChart) (hb : DomainBounded b.toChart) :
    DomainBounded (disjointUnion a b hd).toChart := by
  obtain ⟨β, hβ⟩ := ha
  obtain ⟨γ, hγ⟩ := hb
  refine ⟨max β γ, ?_⟩
  intro u hu i hi
  rcases hu with hua | hub
  · have h := hβ u hua i hi
    exact ⟨(inv_le_inv_iff.mpr (le_max_left β γ)).trans h.1, h.2.trans (le_max_left β γ)⟩
  · have h := hγ u hub i hi
    exact ⟨(inv_le_inv_iff.mpr (le_max_right β γ)).trans h.1, h.2.trans (le_max_right β γ)⟩

def boundedUnion {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain)
    (ha : DomainBounded a.toChart) (hb : DomainBounded b.toChart) : RVBoundedCharts.BoundedChart B k :=
  ⟨(disjointUnion a b hd).toChart, domain_bounded a b hd ha hb⟩

theorem ordinary_class {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain) :
    RVOrdinaryRing.objectClass (disjointUnion a b hd).toChart =
      RVOrdinaryRing.objectClass a.toChart + RVOrdinaryRing.objectClass b.toChart := by
  have hs := RVOrdinaryRing.objectClass_scissor _ _ _ _
    (RVForgetScissors.measured_scissor _ _ _ _ (scissor a b hd))
  rw [RVOrdinaryRing.objectClass_empty (empty B n k).toChart rfl, add_zero] at hs
  exact hs

theorem res_class {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain)
    (ha : (Set.range a.toChart.valuePattern).Finite) (hb : (Set.range b.toChart.valuePattern).Finite) :
    RESChartRing.objectClass (resUnion a b hd ha hb) =
      RESChartRing.objectClass (⟨a.toChart, ha⟩ : RESChart B k) +
        RESChartRing.objectClass (⟨b.toChart, hb⟩ : RESChart B k) := by
  let e : RESChart B k := ⟨(empty B n k).toChart, Chart.finite_domain_values _ Set.finite_empty⟩
  have hs := RESChartRing.objectClass_scissor (⟨a.toChart, ha⟩ : RESChart B k)
    (⟨b.toChart, hb⟩ : RESChart B k) (resUnion a b hd ha hb) e (scissor a b hd)
  rw [RESChartRing.objectClass_empty e rfl, add_zero] at hs
  exact hs

theorem ordinary_res_class {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain)
    (ha : (Set.range a.toChart.valuePattern).Finite) (hb : (Set.range b.toChart.valuePattern).Finite) :
    RESOrdinaryRing.objectClass (resUnion a b hd ha hb) =
      RESOrdinaryRing.objectClass (⟨a.toChart, ha⟩ : RESChart B k) +
        RESOrdinaryRing.objectClass (⟨b.toChart, hb⟩ : RESChart B k) := by
  have he := congrArg (RESOrdinaryRing.forget B) (res_class a b hd ha hb)
  simpa only [map_add, RESOrdinaryRing.forget_objectClass] using he

theorem bounded_class {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : Disjoint a.domain b.domain)
    (ha : DomainBounded a.toChart) (hb : DomainBounded b.toChart) :
    RVBoundedRing.objectClass (boundedUnion a b hd ha hb) =
      RVBoundedRing.objectClass (⟨a.toChart, ha⟩ : RVBoundedCharts.BoundedChart B k) +
        RVBoundedRing.objectClass (⟨b.toChart, hb⟩ : RVBoundedCharts.BoundedChart B k) := by
  let e : RVBoundedCharts.BoundedChart B k := ⟨(empty B n k).toChart, ⟨1, fun _ h => h.elim⟩⟩
  have hs := RVBoundedRing.objectClass_scissor (⟨a.toChart, ha⟩ : RVBoundedCharts.BoundedChart B k)
    (⟨b.toChart, hb⟩ : RVBoundedCharts.BoundedChart B k) (boundedUnion a b hd ha hb) e (scissor a b hd)
  rw [RVBoundedRing.objectClass_empty e rfl, add_zero] at hs
  exact hs

end DiamondIntegral.Section4.RVChartUnionProperties
