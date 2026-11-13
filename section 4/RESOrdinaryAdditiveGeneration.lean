import «section 4».RESOrdinaryGrading
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-! Products of actual RES objects are actual RES objects. Consequently
their classes generate the ordinary chart ring as an additive group. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESOrdinaryAdditiveGeneration
open RVMeasuredCharts RESOrdinaryRing
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def span (B : Base (M := M)) : AddSubgroup (Ring B) :=
  AddSubgroup.closure (Set.range (fun a : Generator B => objectClass a.2))

theorem class_mem (B : Base (M := M)) {k : ℕ} (a : RESChart B k) : objectClass a ∈ span B :=
  AddSubgroup.subset_closure ⟨⟨k, a⟩, rfl⟩

theorem mul_mem (B : Base (M := M)) {x y : Ring B} (hx : x ∈ span B) (hy : y ∈ span B) :
    x * y ∈ span B := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨k, a⟩, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨l, b⟩, rfl⟩ := hy
      rw [← objectClass_product]
      exact class_mem B _
    | zero => simpa only [mul_zero] using (span B).zero_mem
    | add y z _ _ hy hz => simpa only [mul_add] using (span B).add_mem hy hz
    | neg y _ hy => simpa only [mul_neg] using (span B).neg_mem hy
  | zero => simpa only [zero_mul] using (span B).zero_mem
  | add x z _ _ hx hz => simpa only [add_mul] using (span B).add_mem hx hz
  | neg x _ hx => simpa only [neg_mul] using (span B).neg_mem hx

theorem mem_span (B : Base (M := M)) (x : Ring B) : x ∈ span B := by
  let q : FreeCommRing (Generator B) →+* Ring B := Ideal.Quotient.mk (relationIdeal B)
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective x
  change q p = x at hp
  rw [← hp]
  clear hp x
  induction p using FreeCommRing.induction_on with
  | neg_one =>
    rw [map_neg, map_one, ← objectClass_unit B]
    exact (span B).neg_mem (class_mem B _)
  | of a => exact class_mem B a.2
  | add p q hp hq => simpa only [map_add] using (span B).add_mem hp hq
  | mul p q hp hq => simpa only [map_mul] using mul_mem B hp hq

theorem induction (B : Base (M := M)) (P : AddSubgroup (Ring B))
    (h : ∀ k (a : RESChart B k), objectClass a ∈ P) (x : Ring B) : x ∈ P := by
  apply (show span B ≤ P from (AddSubgroup.closure_le P).mpr ?_) (mem_span B x)
  rintro _ ⟨⟨k, a⟩, rfl⟩
  exact h k a

end DiamondIntegral.Section4.RESOrdinaryAdditiveGeneration
