import «section 4».RVFiniteWeightedCounts
import «section 4».RVForgetScissors
import Mathlib.Algebra.MonoidAlgebra.Lift

/-! Ordinary integer counts of actual finite RV domains. They forget
weights, respect underlying bijections and ordinary scissors, and are
multiplicative. No definable splitting into RV points is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVFiniteOrdinaryCounts
open RVMeasuredCharts RVForgetScissors
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def augmentation (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] : RVFiniteWeightedCounts.Target M →+* ℤ :=
  MonoidAlgebra.liftNCRingHom (RingHom.id ℤ) (1 : Values.Gamma (M := M) →* ℤ) (fun _ _ => Commute.all _ _)

def count {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) : ℤ :=
  augmentation M (RVFiniteWeightedCounts.count a ha)

theorem count_eq_sum {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) :
    count a ha = ∑ _u ∈ ha.toFinset, (1 : ℤ) := by
  unfold count RVFiniteWeightedCounts.count
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [augmentation, MonoidAlgebra.liftNCRingHom_single, RingHom.id_apply, MonoidHom.one_apply, one_mul]

theorem count_iso {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (ha : a.domain.Finite) (hb : b.domain.Finite)
    (f : UnderlyingIso a b) : count a ha = count b hb := by
  rw [count_eq_sum, count_eq_sum]
  apply Finset.sum_bij (fun u hu => (f.equiv ⟨u, ha.mem_toFinset.mp hu⟩).val)
  · intro u hu
    exact hb.mem_toFinset.mpr (f.equiv ⟨u, ha.mem_toFinset.mp hu⟩).property
  · intro u hu v hv he
    exact congrArg Subtype.val (f.equiv.injective (Subtype.ext he))
  · intro v hv
    exact ⟨(f.equiv.symm ⟨v, hb.mem_toFinset.mp hv⟩).val,
      ha.mem_toFinset.mpr (f.equiv.symm ⟨v, hb.mem_toFinset.mp hv⟩).property,
      congrArg Subtype.val (f.equiv.apply_symm_apply _)⟩
  · intro _ _
    rfl

theorem packedDomain_finite {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) : (packedDomain a).Finite := by
  rw [packedDomain_eq_image]
  exact (RVFiniteWeightedCounts.packed_finite a ha).image _

theorem count_packedDomain {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) :
    count a ha = ∑ _p ∈ (packedDomain_finite a ha).toFinset, (1 : ℤ) := by
  rw [count_eq_sum]
  apply Finset.sum_bij (fun u _ => (⟨a.arity, u⟩ : Σ n : ℕ, Fin n → M))
  · intro u hu
    exact (packedDomain_finite a ha).mem_toFinset.mpr ⟨⟨u, ha.mem_toFinset.mp hu⟩, rfl⟩
  · intro u hu v hv he
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  · intro p hp
    obtain ⟨u, hu⟩ := (packedDomain_finite a ha).mem_toFinset.mp hp
    exact ⟨u.val, ha.mem_toFinset.mpr u.property, hu⟩
  · intro _ _
    rfl

theorem count_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k)
    (ha : a.domain.Finite) (hb : b.domain.Finite) (hc : c.domain.Finite) (hd : d.domain.Finite)
    (h : Scissor a b c d) : count c hc + count d hd = count a ha + count b hb := by
  rw [count_packedDomain, count_packedDomain, count_packedDomain, count_packedDomain]
  have hu : (packedDomain_finite c hc).toFinset = (packedDomain_finite a ha).toFinset ∪ (packedDomain_finite b hb).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, h.2.2.2.1, Set.mem_union]
  have hi : (packedDomain_finite d hd).toFinset = (packedDomain_finite a ha).toFinset ∩ (packedDomain_finite b hb).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Finset.mem_inter, h.2.2.2.2, Set.mem_inter_iff]
  rw [hu, hi]
  exact Finset.sum_union_inter

theorem count_product {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l) (ha : a.domain.Finite) (hb : b.domain.Finite) :
    count (RVMeasuredProduct.product a b) (RVFiniteWeightedCounts.product_domain_finite a b ha hb) = count a ha * count b hb := by
  unfold count
  rw [RVFiniteWeightedCounts.count_product, map_mul]

theorem count_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain.Finite) (he : a.domain = ∅) : count a ha = 0 := by
  unfold count
  rw [RVFiniteWeightedCounts.count_empty a ha he, map_zero]

theorem count_weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : GammaDefinableClosureAtBase B γ) :
    count (weightedUnit B γ hγ) (weightedUnit B γ hγ).zero_domain_finite = 1 := by
  unfold count
  rw [RVFiniteWeightedCounts.count_weightedUnit]
  simp only [augmentation, MonoidAlgebra.liftNCRingHom_single, RingHom.id_apply, MonoidHom.one_apply, one_mul]

end DiamondIntegral.Section4.RVFiniteOrdinaryCounts
