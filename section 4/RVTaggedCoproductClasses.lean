import «section 4».RVTaggedCoproductProperties

/-! Tagged coproducts have the sum of the original classes in the actual
measured RES, ordinary RES and bounded measured RV presentations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVTaggedCoproductClasses
open RVMeasuredCharts RVMeasuredBounds RVMeasuredProductProperties RVChartDisjointUnion RVNamedTuples
open RVTaggedCoproduct RVTaggedCoproductProperties
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem castGrade_res_class {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k)
    (ha : (Set.range a.toChart.valuePattern).Finite) :
    RESChartRing.objectClass (⟨(castGrade h a).toChart, (castGrade_finite_iff h a).mpr ha⟩ : RESChart B l) =
      RESChartRing.objectClass (⟨a.toChart, ha⟩ : RESChart B k) := by
  cases h
  rfl

def leftRES {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) : RESChart B k :=
  ⟨(leftData a.toChart b.toChart).toChart, left_finite_patterns a b⟩

def rightRES {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) : RESChart B k :=
  ⟨(rightData a.toChart b.toChart).toChart, right_finite_patterns a b⟩

theorem left_res_class {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    RESChartRing.objectClass (leftRES a b) = RESChartRing.objectClass a := by
  let r : RESChart B (0 + k) := resProduct (resProduct (zeroTagRES B) a) (zerosRES B b.arity)
  have he := castGrade_res_class (Nat.zero_add k) (leftRawData a.toChart b.toChart) r.finite_values
  change RESChartRing.objectClass (leftRES a b) = RESChartRing.objectClass r at he
  apply he.trans
  change RESChartRing.objectClass (resProduct (resProduct (zeroTagRES B) a) (zerosRES B b.arity)) = _
  rw [RESChartRing.objectClass_product, RESChartRing.objectClass_product]
  have ht : RESChartRing.objectClass (zeroTagRES B) = 1 := tuple_res_class B ![iRVZero]
    (by intro i; fin_cases i; exact zero_definable B)
  have hz : RESChartRing.objectClass (zerosRES B b.arity) = 1 :=
    tuple_res_class B (fun _ : Fin b.arity => iRVZero) (fun _ => zero_definable B)
  rw [ht, hz, one_mul, mul_one]

theorem right_res_class {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    RESChartRing.objectClass (rightRES a b) = RESChartRing.objectClass b := by
  change RESChartRing.objectClass (resProduct (resProduct (oneTagRES B) (zerosRES B a.arity)) b) = _
  rw [RESChartRing.objectClass_product, RESChartRing.objectClass_product]
  have ht : RESChartRing.objectClass (oneTagRES B) = 1 := tuple_res_class B ![iRVOne]
    (by intro i; fin_cases i; exact one_definable B)
  have hz : RESChartRing.objectClass (zerosRES B a.arity) = 1 :=
    tuple_res_class B (fun _ : Fin a.arity => iRVZero) (fun _ => zero_definable B)
  rw [ht, hz, one_mul, one_mul]

theorem res_coproduct_class {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    RESChartRing.objectClass (resCoproduct a b) = RESChartRing.objectClass a + RESChartRing.objectClass b := by
  have he := RVChartUnionProperties.res_class (leftData a.toChart b.toChart) (rightData a.toChart b.toChart)
    (tagged_disjoint a.toChart b.toChart) (left_finite_patterns a b) (right_finite_patterns a b)
  change RESChartRing.objectClass (resCoproduct a b) =
    RESChartRing.objectClass (leftRES a b) + RESChartRing.objectClass (rightRES a b) at he
  rw [left_res_class, right_res_class] at he
  exact he

theorem ordinary_res_coproduct_class {B : Base (M := M)} {k : ℕ} (a b : RESChart B k) :
    RESOrdinaryRing.objectClass (resCoproduct a b) = RESOrdinaryRing.objectClass a + RESOrdinaryRing.objectClass b := by
  have he := congrArg (RESOrdinaryRing.forget B) (res_coproduct_class a b)
  simpa only [map_add, RESOrdinaryRing.forget_objectClass] using he

theorem castGrade_bounded_class {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k)
    (ha : DomainBounded a.toChart) :
    RVBoundedRing.objectClass (⟨(castGrade h a).toChart, (castGrade_bounded_iff h a).mpr ha⟩ : RVBoundedCharts.BoundedChart B l) =
      RVBoundedRing.objectClass (⟨a.toChart, ha⟩ : RVBoundedCharts.BoundedChart B k) := by
  cases h
  rfl

theorem bounded_tuple_class (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) :
    RVBoundedRing.objectClass (RVBoundedCharts.ofRES (tupleRESChart B x hx)) = 1 :=
  (RVBoundedRing.objectClass_iso (tupleUnitIso B x hx)).trans (RVBoundedRing.objectClass_unit B)

def leftBounded {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) : RVBoundedCharts.BoundedChart B k :=
  ⟨(leftData a.toChart b.toChart).toChart, left_domain_bounded a b⟩

def rightBounded {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) : RVBoundedCharts.BoundedChart B k :=
  ⟨(rightData a.toChart b.toChart).toChart, right_domain_bounded a b⟩

theorem left_bounded_class {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) :
    RVBoundedRing.objectClass (leftBounded a b) = RVBoundedRing.objectClass a := by
  let r : RVBoundedCharts.BoundedChart B (0 + k) := RVBoundedCharts.product
    (RVBoundedCharts.product (RVBoundedCharts.ofRES (zeroTagRES B)) a) (RVBoundedCharts.ofRES (zerosRES B b.arity))
  have he := castGrade_bounded_class (Nat.zero_add k) (leftRawData a.toChart b.toChart) r.domain_bounded
  change RVBoundedRing.objectClass (leftBounded a b) = RVBoundedRing.objectClass r at he
  apply he.trans
  change RVBoundedRing.objectClass (RVBoundedCharts.product
    (RVBoundedCharts.product (RVBoundedCharts.ofRES (zeroTagRES B)) a) (RVBoundedCharts.ofRES (zerosRES B b.arity))) = _
  rw [RVBoundedRing.objectClass_product, RVBoundedRing.objectClass_product]
  have ht : RVBoundedRing.objectClass (RVBoundedCharts.ofRES (zeroTagRES B)) = 1 :=
    bounded_tuple_class B ![iRVZero] (by intro i; fin_cases i; exact zero_definable B)
  have hz : RVBoundedRing.objectClass (RVBoundedCharts.ofRES (zerosRES B b.arity)) = 1 :=
    bounded_tuple_class B (fun _ : Fin b.arity => iRVZero) (fun _ => zero_definable B)
  rw [ht, hz, one_mul, mul_one]

theorem right_bounded_class {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) :
    RVBoundedRing.objectClass (rightBounded a b) = RVBoundedRing.objectClass b := by
  change RVBoundedRing.objectClass (RVBoundedCharts.product
    (RVBoundedCharts.product (RVBoundedCharts.ofRES (oneTagRES B)) (RVBoundedCharts.ofRES (zerosRES B a.arity))) b) = _
  rw [RVBoundedRing.objectClass_product, RVBoundedRing.objectClass_product]
  have ht : RVBoundedRing.objectClass (RVBoundedCharts.ofRES (oneTagRES B)) = 1 :=
    bounded_tuple_class B ![iRVOne] (by intro i; fin_cases i; exact one_definable B)
  have hz : RVBoundedRing.objectClass (RVBoundedCharts.ofRES (zerosRES B a.arity)) = 1 :=
    bounded_tuple_class B (fun _ : Fin a.arity => iRVZero) (fun _ => zero_definable B)
  rw [ht, hz, one_mul, one_mul]

theorem bounded_coproduct_class {B : Base (M := M)} {k : ℕ} (a b : RVBoundedCharts.BoundedChart B k) :
    RVBoundedRing.objectClass (boundedCoproduct a b) = RVBoundedRing.objectClass a + RVBoundedRing.objectClass b := by
  have he := RVChartUnionProperties.bounded_class (leftData a.toChart b.toChart) (rightData a.toChart b.toChart)
    (tagged_disjoint a.toChart b.toChart) (left_domain_bounded a b) (right_domain_bounded a b)
  change RVBoundedRing.objectClass (boundedCoproduct a b) =
    RVBoundedRing.objectClass (leftBounded a b) + RVBoundedRing.objectClass (rightBounded a b) at he
  rw [left_bounded_class, right_bounded_class] at he
  exact he

end DiamondIntegral.Section4.RVTaggedCoproductClasses
