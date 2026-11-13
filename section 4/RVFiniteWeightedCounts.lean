import «section 4».RVMeasuredProductProperties
import «section 4».RVMeasuredGroup
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite actual RV domains admit a weighted cardinality in the full
Gamma group ring. This is a numerical invariant of finite sets, not a
decomposition into definable RV singletons. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped BigOperators

namespace DiamondIntegral.Section4.RVFiniteWeightedCounts
open RVMeasuredCharts RVMeasuredGroup FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Target (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] := MonoidAlgebra ℤ (Values.Gamma (M := M))

def count {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) : Target M :=
  ∑ u ∈ ha.toFinset, MonoidAlgebra.single (a.correctedWeight u) (1 : ℤ)

theorem count_iso {B : Base (M := M)} {k : ℕ} {a b : Chart B k}
    (ha : a.domain.Finite) (hb : b.domain.Finite) (F : Iso a b) : count a ha = count b hb := by
  unfold count
  apply Finset.sum_bij (fun u hu => (F.equiv ⟨u, ha.mem_toFinset.mp hu⟩).val)
  · intro u hu
    exact hb.mem_toFinset.mpr (F.equiv ⟨u, ha.mem_toFinset.mp hu⟩).property
  · intro u hu v hv he
    exact congrArg Subtype.val (F.equiv.injective (Subtype.ext he))
  · intro v hv
    refine ⟨(F.equiv.symm ⟨v, hb.mem_toFinset.mp hv⟩).val,
      ha.mem_toFinset.mpr (F.equiv.symm ⟨v, hb.mem_toFinset.mp hv⟩).property, ?_⟩
    exact congrArg Subtype.val (F.equiv.apply_symm_apply _)
  · intro u hu
    exact congrArg (fun γ => (MonoidAlgebra.single γ (1 : ℤ) : Target M)) (F.weight_eq ⟨u, ha.mem_toFinset.mp hu⟩)

def packing {B : Base (M := M)} {k : ℕ} (a : Chart B k) (u : Fin a.arity → M) :
    Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M) := ⟨a.arity, u, a.correctedWeight u⟩

theorem packing_injective {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Function.Injective (packing a) := by
  intro u v h
  have hp : (u, a.correctedWeight u) = (v, a.correctedWeight v) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact congrArg Prod.fst hp

theorem packed_eq_image {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    packed a = packing a '' a.domain := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, u.property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

theorem packed_finite {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) : (packed a).Finite := by
  rw [packed_eq_image]
  exact ha.image _

theorem count_packed {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) :
    count a ha = ∑ p ∈ (packed_finite a ha).toFinset, (MonoidAlgebra.single p.2.2 (1 : ℤ) : Target M) := by
  have he : (packed_finite a ha).toFinset = ha.toFinset.image (packing a) := by
    ext p
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, packed_eq_image, Set.mem_image]
  rw [he, Finset.sum_image]
  · rfl
  · exact (packing_injective a).injOn

theorem count_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k)
    (ha : a.domain.Finite) (he : a.domain = ∅) : count a ha = 0 := by
  have hf : ha.toFinset = ∅ := by ext u; simp [he]
  simp only [count, hf, Finset.sum_empty]

theorem count_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k)
    (ha : a.domain.Finite) (hb : b.domain.Finite) (hc : c.domain.Finite) (hd : d.domain.Finite)
    (h : Scissor a b c d) : count c hc + count d hd = count a ha + count b hb := by
  rw [count_packed, count_packed, count_packed, count_packed]
  have hu : (packed_finite c hc).toFinset = (packed_finite a ha).toFinset ∪ (packed_finite b hb).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, h.2.2.2.1, Set.mem_union]
  have hi : (packed_finite d hd).toFinset = (packed_finite a ha).toFinset ∩ (packed_finite b hb).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Finset.mem_inter, h.2.2.2.2, Set.mem_inter_iff]
  rw [hu, hi]
  exact Finset.sum_union_inter

theorem product_domain_finite {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (ha : a.domain.Finite) (hb : b.domain.Finite) : (RVMeasuredProduct.product a b).domain.Finite := by
  have he : (RVMeasuredProduct.product a b).domain =
      (fun p : (Fin a.arity → M) × (Fin b.arity → M) => join b.arity a.arity p.1 p.2) ''
        (a.domain ×ˢ b.domain) := by
    change RVRealProducts.productSet a.domain b.domain = _
    ext z
    rw [RVRealProducts.productSet_exists]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
      exact ⟨u, hu, v, hv, rfl⟩
  rw [he]
  exact (ha.prod hb).image _

theorem count_product {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l)
    (ha : a.domain.Finite) (hb : b.domain.Finite) :
    count (RVMeasuredProduct.product a b) (product_domain_finite a b ha hb) = count a ha * count b hb := by
  unfold count
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product (f := fun p : (Fin a.arity → M) × (Fin b.arity → M) =>
    MonoidAlgebra.single (a.correctedWeight p.1) (1 : ℤ) * MonoidAlgebra.single (b.correctedWeight p.2) (1 : ℤ))]
  symm
  apply Finset.sum_bij (fun p _ => join b.arity a.arity p.1 p.2)
  · intro p hp
    exact (product_domain_finite a b ha hb).mem_toFinset.mpr
      ((RVRealProducts.productSet_join _ _ _ _).mpr
        ⟨ha.mem_toFinset.mp (Finset.mem_product.mp hp).1, hb.mem_toFinset.mp (Finset.mem_product.mp hp).2⟩)
  · intro p hp q hq he
    apply Prod.ext
    · funext i
      simpa only [join_head] using congrFun he (headIndex b.arity a.arity i)
    · funext i
      simpa only [join_tail] using congrFun he (tailIndex b.arity a.arity i)
  · intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := (RVRealProducts.productSet_exists _ _ z).mp
      ((product_domain_finite a b ha hb).mem_toFinset.mp hz)
    exact ⟨(u, v), Finset.mem_product.mpr ⟨ha.mem_toFinset.mpr hu, hb.mem_toFinset.mpr hv⟩, rfl⟩
  · intro p hp
    rw [MonoidAlgebra.single_mul_single, one_mul]
    exact congrArg (fun γ => (MonoidAlgebra.single γ (1 : ℤ) : Target M))
      (RVMeasuredProductProperties.product_weight_join a b p.1 p.2).symm

theorem count_singleton {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite)
    (u : Fin a.arity → M) (hu : a.domain = {u}) : count a ha = MonoidAlgebra.single (a.correctedWeight u) 1 := by
  have he : ha.toFinset = {u} := by
    ext v
    simp only [Set.Finite.mem_toFinset, hu, Set.mem_singleton_iff, Finset.mem_singleton]
  simp only [count, he, Finset.sum_singleton]

theorem count_weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) :
    count (weightedUnit B γ hγ) (weightedUnit B γ hγ).zero_domain_finite = MonoidAlgebra.single γ 1 := by
  rw [count_singleton (weightedUnit B γ hγ) _ Fin.elim0 (by
    ext u
    change True ↔ u = Fin.elim0
    exact ⟨fun _ => @Subsingleton.elim (Fin 0 → M) inferInstance _ _, fun _ => trivial⟩)]
  rw [weightedUnit_correctedWeight]

end DiamondIntegral.Section4.RVFiniteWeightedCounts
