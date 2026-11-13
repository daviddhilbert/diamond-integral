import «section 4».RVTaggedCoproduct
import «section 4».RVMeasuredProductProperties

/-! Actual tagged RV coproducts retain finite RES value patterns and
bounded domains. Their ordinary RV classes also add. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVTaggedCoproductProperties
open RVMeasuredCharts RVMeasuredBounds RVMeasuredProductProperties RVChartDisjointUnion RVNamedTuples RVTaggedCoproduct
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem castGrade_finite_iff {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k) :
    (Set.range (castGrade h a).toChart.valuePattern).Finite ↔ (Set.range a.toChart.valuePattern).Finite := by
  cases h
  rfl

theorem castGrade_bounded_iff {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k) :
    DomainBounded (castGrade h a).toChart ↔ DomainBounded a.toChart := by
  cases h
  rfl

def zeroTagRES (B : Base (M := M)) : RESChart B 0 :=
  tupleRESChart B ![iRVZero] (by intro i; fin_cases i; exact zero_definable B)

def oneTagRES (B : Base (M := M)) : RESChart B 0 :=
  tupleRESChart B ![iRVOne] (by intro i; fin_cases i; exact one_definable B)

def zerosRES (B : Base (M := M)) (n : ℕ) : RESChart B 0 :=
  tupleRESChart B (fun _ : Fin n => iRVZero) (fun _ => zero_definable B)

theorem left_finite_patterns {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    (Set.range (leftData a.toChart b.toChart).toChart.valuePattern).Finite := by
  apply (castGrade_finite_iff (Nat.zero_add k) (leftRawData a.toChart b.toChart)).mpr
  exact product_finite_patterns (resProduct (zeroTagRES B) a) (zerosRES B b.arity)

theorem right_finite_patterns {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    (Set.range (rightData a.toChart b.toChart).toChart.valuePattern).Finite :=
  product_finite_patterns (resProduct (oneTagRES B) (zerosRES B a.arity)) b

def resCoproduct {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) : RESChart B k :=
  ⟨coproduct a.toChart b.toChart, RVChartUnionProperties.finite_patterns _ _ (tagged_disjoint a.toChart b.toChart)
    (left_finite_patterns a b) (right_finite_patterns a b)⟩

theorem left_domain_bounded {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) :
    DomainBounded (leftData a.toChart b.toChart).toChart := by
  apply (castGrade_bounded_iff (Nat.zero_add k) (leftRawData a.toChart b.toChart)).mpr
  exact product_domain_bounded _ _
    (product_domain_bounded _ _ (res_domain_bounded (zeroTagRES B)) a.domain_bounded)
    (res_domain_bounded (zerosRES B b.arity))

theorem right_domain_bounded {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) :
    DomainBounded (rightData a.toChart b.toChart).toChart :=
  product_domain_bounded _ _
    (product_domain_bounded _ _ (res_domain_bounded (oneTagRES B)) (res_domain_bounded (zerosRES B a.arity))) b.domain_bounded

def boundedCoproduct {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) : RVBoundedCharts.BoundedChart B k :=
  ⟨coproduct a.toChart b.toChart, RVChartUnionProperties.domain_bounded _ _ (tagged_disjoint a.toChart b.toChart)
    (left_domain_bounded a b) (right_domain_bounded a b)⟩

theorem ordinary_class_coproduct {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    RVOrdinaryRing.objectClass (coproduct a b) = RVOrdinaryRing.objectClass a + RVOrdinaryRing.objectClass b := by
  have he := congrArg (RVOrdinaryRing.forget B) (class_coproduct a b)
  simpa only [map_add, RVOrdinaryRing.forget_objectClass] using he

end DiamondIntegral.Section4.RVTaggedCoproductProperties
