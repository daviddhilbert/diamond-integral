import «section 4».GammaNameTuples
import «section 4».GammaRVIdentityIso
import «section 4».GammaFiniteRVPresentation

/-! Finite Gamma chart classes split as finite sums of original-base
named singleton charts with constant weights. This splits Gamma sets;
it does not split finite RV sets into definable points. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteDecomposition
open GammaNameTuples GammaFiniteRVCharts GammaFiniteRVPresentation
open GammaOrderLogic GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem class_eq_on_domain {B : Base (M := M)} {n : ℕ} (a b : FiniteChart B n)
    (hs : a.support = b.support) (hv : ∀ z ∈ a.support, a.volume z = b.volume z) :
    objectClass a = objectClass b :=
  class_iso (GammaRVIdentityIso.sameDomainIso a.toChart b.toChart hs hv)

theorem class_normalized {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) :
    objectClass a = objectClass (GammaFiniteRVCharts.ofTotal B n a.support a.support_definable a.finite_support
      a.toChart.normalizedVolume a.toChart.normalizedVolume_definable) :=
  class_iso (GammaRVIdentityIso.normalizedIso a.toChart)

def setChart {B : Base (M := M)} {n : ℕ} (s : Finset (NameTuple B n))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : FiniteChart B n :=
  GammaFiniteRVCharts.ofTotal B n (support s) (support_definable s) (s.finite_toSet.image GammaNameTuples.values) μ hμ

def pointChart {B : Base (M := M)} {n : ℕ} (α : NameTuple B n)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : FiniteChart B n :=
  GammaFiniteRVCharts.ofTotal B n {GammaNameTuples.values α} (GammaNameTuples.singleton_definable α) (Set.finite_singleton _) μ hμ

def constantChart {B : Base (M := M)} {n : ℕ} (α : NameTuple B n)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : FiniteChart B n :=
  GammaFiniteRVCharts.ofTotal B n {GammaNameTuples.values α} (GammaNameTuples.singleton_definable α) (Set.finite_singleton _)
    (fun _ => μ (GammaNameTuples.values α)) (constant_definable B _ (scalar_value_definable α μ hμ))

theorem setChart_class_empty (B : Base (M := M)) (n : ℕ)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (setChart (∅ : Finset (NameTuple B n)) μ hμ) = 0 :=
  (class_eq_on_domain (setChart (∅ : Finset (NameTuple B n)) μ hμ) (GammaFiniteRVCharts.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) Set.finite_empty μ hμ)
    (support_empty B n) (fun _ _ => rfl)).trans (class_empty B n μ hμ)

theorem setChart_class_insert {B : Base (M := M)} {n : ℕ} (α : NameTuple B n) (s : Finset (NameTuple B n))
    (hα : α ∉ s) (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (setChart (insert α s) μ hμ) = objectClass (pointChart α μ hμ) + objectClass (setChart s μ hμ) := by
  have hU : GammaDefinable B ({GammaNameTuples.values α} ∪ support s) := (support_insert α s) ▸ support_definable (insert α s)
  have hN := GammaRelationLogic.inter_definable_base B {GammaNameTuples.values α} (support s)
    (GammaNameTuples.singleton_definable α) (support_definable s)
  let u := GammaFiniteRVCharts.ofTotal B n ({GammaNameTuples.values α} ∪ support s) hU ((Set.finite_singleton _).union (s.finite_toSet.image GammaNameTuples.values)) μ hμ
  let d := GammaFiniteRVCharts.ofTotal B n ({GammaNameTuples.values α} ∩ support s) hN ((Set.finite_singleton _).subset Set.inter_subset_left) μ hμ
  have hu : objectClass (setChart (insert α s) μ hμ) = objectClass u :=
    class_eq_on_domain (setChart (insert α s) μ hμ) u (support_insert α s) (fun _ _ => rfl)
  have hd : objectClass d = 0 :=
    (class_eq_on_domain d (GammaFiniteRVCharts.ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) Set.finite_empty μ hμ)
      (singleton_inter_support hα) (fun _ _ => rfl)).trans (class_empty B n μ hμ)
  have hc := class_scissor B n {GammaNameTuples.values α} (support s) (GammaNameTuples.singleton_definable α)
    (support_definable s) (Set.finite_singleton _) (s.finite_toSet.image GammaNameTuples.values) hU hN μ hμ
  rw [hd, add_zero] at hc
  exact hu.trans hc

theorem setChart_class_sum {B : Base (M := M)} {n : ℕ} (s : Finset (NameTuple B n))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (setChart s μ hμ) = ∑ α ∈ s, objectClass (pointChart α μ hμ) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using setChart_class_empty B n μ hμ
  | @insert α s hα ih =>
    rw [Finset.sum_insert hα]
    exact (setChart_class_insert α s hα μ hμ).trans (congrArg (objectClass (pointChart α μ hμ) + ·) ih)

theorem pointChart_class_constant {B : Base (M := M)} {n : ℕ} (α : NameTuple B n)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (pointChart α μ hμ) = objectClass (constantChart α μ hμ) := by
  apply class_eq_on_domain (pointChart α μ hμ) (constantChart α μ hμ) rfl
  intro z hz
  have he : z = GammaNameTuples.values α := hz
  change μ z = μ (GammaNameTuples.values α)
  rw [he]

theorem setChart_class_sum_constants {B : Base (M := M)} {n : ℕ} (s : Finset (NameTuple B n))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectClass (setChart s μ hμ) = ∑ α ∈ s, objectClass (constantChart α μ hμ) := by
  refine (setChart_class_sum s μ hμ).trans (Finset.sum_congr rfl ?_)
  intro α _
  exact pointChart_class_constant α μ hμ

theorem finite_class_decomposition {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) :
    ∃ s : Finset (NameTuple B n), support s = a.support ∧
      objectClass a = ∑ α ∈ s, objectClass (constantChart α a.toChart.normalizedVolume a.toChart.normalizedVolume_definable) := by
  obtain ⟨s, hs⟩ := finite_support_representation B a.support a.support_definable a.finite_support
  refine ⟨s, hs, ?_⟩
  have he : objectClass (GammaFiniteRVCharts.ofTotal B n a.support a.support_definable a.finite_support
      a.toChart.normalizedVolume a.toChart.normalizedVolume_definable) =
      objectClass (setChart s a.toChart.normalizedVolume a.toChart.normalizedVolume_definable) :=
    class_eq_on_domain
      (GammaFiniteRVCharts.ofTotal B n a.support a.support_definable a.finite_support
        a.toChart.normalizedVolume a.toChart.normalizedVolume_definable)
      (setChart s a.toChart.normalizedVolume a.toChart.normalizedVolume_definable) hs.symm (fun _ _ => rfl)
  exact (class_normalized a).trans (he.trans (setChart_class_sum_constants s a.toChart.normalizedVolume a.toChart.normalizedVolume_definable))

end DiamondIntegral.Section4.GammaFiniteDecomposition
