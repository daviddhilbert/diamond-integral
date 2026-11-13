import «section 4».RVNamedTuples
import «section 4».RVChartUnionProperties

/-! Actual finite RV tags and padding put any two same-degree charts
into disjoint domains of a common tuple arity. Their union has the sum of
the original measured RV classes. No RV section or new base is chosen. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVTaggedCoproduct
open RVMeasuredCharts RVMeasuredProduct RVChartDisjointUnion RVNamedTuples FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def leftRawData {B : Base (M := M)} {k : ℕ} (a b : Chart B k) : Data B (b.arity + (a.arity + 1)) (0 + k) :=
  ofChart (product (product (tagZero B) a) (zeros B b.arity))

def leftData {B : Base (M := M)} {k : ℕ} (a b : Chart B k) : Data B (b.arity + (a.arity + 1)) k :=
  castGrade (Nat.zero_add k) (leftRawData a b)

def rightData {B : Base (M := M)} {k : ℕ} (a b : Chart B k) : Data B (b.arity + (a.arity + 1)) k :=
  ofChart (product (product (tagOne B) (zeros B a.arity)) b)

theorem left_tag {B : Base (M := M)} {k : ℕ} (a b : Chart B k)
    (u : Fin (b.arity + (a.arity + 1)) → M) (hu : u ∈ (leftData a b).domain) : u 0 = iRVZero := by
  rw [leftData, castGrade_domain] at hu
  change u ∈ (product (product (tagZero B) a) (zeros B b.arity)).domain at hu
  have he := congrFun hu.1.1 (0 : Fin 1)
  exact he

theorem right_tag {B : Base (M := M)} {k : ℕ} (a b : Chart B k)
    (u : Fin (b.arity + (a.arity + 1)) → M) (hu : u ∈ (rightData a b).domain) : u 0 = iRVOne := by
  have he := congrFun hu.1.1 (0 : Fin 1)
  exact he

theorem tagged_disjoint {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    Disjoint (leftData a b).domain (rightData a b).domain := by
  apply Set.disjoint_left.mpr
  intro u hu hv
  exact RVCalc.rv_one_ne_zero hM ((right_tag a b u hv).symm.trans (left_tag a b u hu))

theorem left_class {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    RVChartRing.objectClass (leftData a b).toChart = RVChartRing.objectClass a := by
  rw [leftData, castGrade_class]
  change RVChartRing.objectClass (product (product (tagZero B) a) (zeros B b.arity)) = _
  rw [RVChartRing.objectClass_product, RVChartRing.objectClass_product]
  have ht : RVChartRing.objectClass (tagZero B) = 1 := tuple_class B ![iRVZero]
    (by intro i; fin_cases i; exact zero_definable B)
  have hz : RVChartRing.objectClass (zeros B b.arity) = 1 :=
    tuple_class B (fun _ : Fin b.arity => iRVZero) (fun _ => zero_definable B)
  rw [ht, hz, one_mul, mul_one]

theorem right_class {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    RVChartRing.objectClass (rightData a b).toChart = RVChartRing.objectClass b := by
  change RVChartRing.objectClass (product (product (tagOne B) (zeros B a.arity)) b) = _
  rw [RVChartRing.objectClass_product, RVChartRing.objectClass_product]
  have ht : RVChartRing.objectClass (tagOne B) = 1 := tuple_class B ![iRVOne]
    (by intro i; fin_cases i; exact one_definable B)
  have hz : RVChartRing.objectClass (zeros B a.arity) = 1 :=
    tuple_class B (fun _ : Fin a.arity => iRVZero) (fun _ => zero_definable B)
  rw [ht, hz, one_mul, one_mul]

def coproduct {B : Base (M := M)} {k : ℕ} (a b : Chart B k) : Chart B k :=
  (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b)).toChart

theorem class_coproduct {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    RVChartRing.objectClass (coproduct a b) = RVChartRing.objectClass a + RVChartRing.objectClass b := by
  change RVChartRing.objectClass (disjointUnion (leftData a b) (rightData a b) (tagged_disjoint a b)).toChart = _
  rw [class_disjointUnion, left_class, right_class]

end DiamondIntegral.Section4.RVTaggedCoproduct
