import «section 4».RVMeasuredCharts
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The fixed-degree additive scissors presentation of actual measured
RV charts. All isomorphisms have the original-base definable graphs and
volume equation from RVMeasuredCharts. Products and identification with
the graded category Grothendieck ring remain separate constructions. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVMeasuredGroup
open RVMeasuredCharts

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def packed {B : Base (M := M)} {k : ℕ} (a : Chart B k) :
    Set (Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)) :=
  Set.range (fun u : a.domain => ⟨a.arity, u.val, a.correctedWeight u.val⟩)

def Scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k) : Prop :=
  a.arity = b.arity ∧ a.arity = c.arity ∧ a.arity = d.arity ∧
    packed c = packed a ∪ packed b ∧ packed d = packed a ∩ packed b

inductive Relation (B : Base (M := M)) (k : ℕ) : FreeAbelianGroup (Chart B k) → Prop where
  | iso (a b : Chart B k) (F : Iso a b) : Relation B k (FreeAbelianGroup.of a - FreeAbelianGroup.of b)
  | empty (a : Chart B k) (h : a.domain = ∅) : Relation B k (FreeAbelianGroup.of a)
  | scissor (a b c d : Chart B k) (h : Scissor a b c d) :
      Relation B k (FreeAbelianGroup.of c + FreeAbelianGroup.of d -
        FreeAbelianGroup.of a - FreeAbelianGroup.of b)

def relationSubgroup (B : Base (M := M)) (k : ℕ) : AddSubgroup (FreeAbelianGroup (Chart B k)) :=
  AddSubgroup.closure {r | Relation B k r}

def KGroup (B : Base (M := M)) (k : ℕ) := FreeAbelianGroup (Chart B k) ⧸ relationSubgroup B k
  deriving AddCommGroup

def objectClass {B : Base (M := M)} {k : ℕ} (a : Chart B k) : KGroup B k :=
  QuotientAddGroup.mk (FreeAbelianGroup.of a)

theorem relation_zero (B : Base (M := M)) (k : ℕ) (r : FreeAbelianGroup (Chart B k))
    (hr : Relation B k r) : (QuotientAddGroup.mk r : KGroup B k) = 0 := by
  exact (QuotientAddGroup.eq_zero_iff r).mpr (AddSubgroup.subset_closure hr)

theorem objectClass_iso {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) :
    objectClass a = objectClass b := by
  have h := relation_zero B k _ (Relation.iso a b F)
  change (QuotientAddGroup.mk' (relationSubgroup B k)) (FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 at h
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) :
    objectClass a = 0 := relation_zero B k _ (.empty a ha)

theorem objectClass_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k) (h : Scissor a b c d) :
    objectClass c + objectClass d = objectClass a + objectClass b := by
  have hr := relation_zero B k _ (Relation.scissor a b c d h)
  change (QuotientAddGroup.mk' (relationSubgroup B k))
    (FreeAbelianGroup.of c + FreeAbelianGroup.of d - FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 at hr
  rw [map_sub, map_sub, map_add, sub_sub] at hr
  exact sub_eq_zero.mp hr

structure Invariant (B : Base (M := M)) (k : ℕ) (A : Type*) [AddCommGroup A] where
  value : Chart B k → A
  iso : ∀ a b (_F : Iso a b), value a = value b
  empty : ∀ a, a.domain = ∅ → value a = 0
  scissor : ∀ a b c d, Scissor a b c d → value c + value d = value a + value b

theorem invariant_relation_zero (B : Base (M := M)) (k : ℕ) {A : Type*} [AddCommGroup A]
    (f : Invariant B k A) (r : FreeAbelianGroup (Chart B k)) (hr : Relation B k r) :
    FreeAbelianGroup.lift f.value r = 0 := by
  cases hr with
  | iso a b F =>
    rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, f.iso a b F, sub_self]
  | empty a h =>
    rw [FreeAbelianGroup.lift_apply_of, f.empty a h]
  | scissor a b c d h =>
    simp only [map_sub, map_add, FreeAbelianGroup.lift_apply_of, sub_sub]
    exact sub_eq_zero.mpr (f.scissor a b c d h)

def lift (B : Base (M := M)) (k : ℕ) {A : Type*} [AddCommGroup A] (f : Invariant B k A) :
    KGroup B k →+ A :=
  QuotientAddGroup.lift (relationSubgroup B k) (FreeAbelianGroup.lift f.value)
    ((AddSubgroup.closure_le (FreeAbelianGroup.lift f.value).ker).mpr
      (fun r hr => invariant_relation_zero B k f r hr))

theorem lift_objectClass (B : Base (M := M)) (k : ℕ) {A : Type*} [AddCommGroup A]
    (f : Invariant B k A) (a : Chart B k) : lift B k f (objectClass a) = f.value a :=
  FreeAbelianGroup.lift_apply_of f.value a

theorem hom_ext (B : Base (M := M)) (k : ℕ) {A : Type*} [AddCommGroup A]
    (f g : KGroup B k →+ A) (h : ∀ a : Chart B k, f (objectClass a) = g (objectClass a)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  exact FreeAbelianGroup.lift_ext _ _ h

theorem lift_unique (B : Base (M := M)) (k : ℕ) {A : Type*} [AddCommGroup A]
    (f : Invariant B k A) (g : KGroup B k →+ A) (h : ∀ a, g (objectClass a) = f.value a) :
    g = lift B k f := by
  apply hom_ext B k
  intro a
  exact (h a).trans (lift_objectClass B k f a).symm

end DiamondIntegral.Section4.RVMeasuredGroup
