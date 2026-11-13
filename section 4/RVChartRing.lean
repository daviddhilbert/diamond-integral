import «section 4».RVMeasuredGroup
import «section 4».RVMeasuredProductProperties
import «section 4».GammaGroupNames
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! A concrete ring presentation on actual measured RV charts, with actual
products, volume-preserving isomorphisms and weighted scissors. Its
identification with the manuscript finite-coproduct category is separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVChartRing
open RVMeasuredCharts RVMeasuredProduct

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Generator (B : Base (M := M)) := Σ k, Chart B k

def symbol {B : Base (M := M)} {k : ℕ} (a : Chart B k) : FreeCommRing (Generator B) :=
  FreeCommRing.of ⟨k, a⟩

def unit (B : Base (M := M)) : Chart B 0 := weightedUnit B 1 (GammaGroupNames.one_definable_base B)

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (unit B) - 1)
  | product {k l : ℕ} (a : Chart B k) (b : Chart B l) :
      Relation B (symbol (product a b) - symbol a * symbol b)
  | iso {k : ℕ} (a b : Chart B k) (F : Iso a b) : Relation B (symbol a - symbol b)
  | empty {k : ℕ} (a : Chart B k) (h : a.domain = ∅) : Relation B (symbol a)
  | scissor {k : ℕ} (a b c d : Chart B k) (h : RVMeasuredGroup.Scissor a b c d) :
      Relation B (symbol c + symbol d - symbol a - symbol b)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}

def Ring (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Ring B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit (B : Base (M := M)) : objectClass (unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    objectClass (product a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) :
    objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) :
    objectClass a = 0 := relation_zero B _ (Relation.empty a ha)

theorem objectClass_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k)
    (h : RVMeasuredGroup.Scissor a b c d) :
    objectClass c + objectClass d = objectClass a + objectClass b := by
  have hr := relation_zero B _ (Relation.scissor a b c d h)
  rw [map_sub, map_sub, map_add, sub_sub] at hr
  exact sub_eq_zero.mp hr

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : ∀ k, Chart B k → R
  unit : value 0 (unit B) = 1
  product : ∀ k l (a : Chart B k) (b : Chart B l), value (l + k) (product a b) = value k a * value l b
  iso : ∀ k (a b : Chart B k) (_F : Iso a b), value k a = value k b
  empty : ∀ k (a : Chart B k), a.domain = ∅ → value k a = 0
  scissor : ∀ k (a b c d : Chart B k), RVMeasuredGroup.Scissor a b c d →
    value k c + value k d = value k a + value k b

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    FreeCommRing (Generator B) →+* R := FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {k : ℕ} (a : Chart B k) : freeMap B f (symbol a) = f.value k a := FreeCommRing.lift_of _ _

theorem invariant_relation_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (r : FreeCommRing (Generator B)) (hr : Relation B r) : freeMap B f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, f.unit, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.product, sub_self]
  | iso a b F => rw [map_sub, freeMap_symbol, freeMap_symbol, f.iso _ a b F, sub_self]
  | empty a h => rw [freeMap_symbol, f.empty _ a h]
  | scissor a b c d h =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (f.scissor _ a b c d h)

theorem invariant_ideal_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    relationIdeal B ≤ RingHom.ker (freeMap B f) := by
  apply Ideal.span_le.mpr
  intro r hr
  exact invariant_relation_zero B f r hr

def lift (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : Ring B →+* R :=
  Ideal.Quotient.lift (relationIdeal B) (freeMap B f) (fun _ hr => invariant_ideal_zero B f hr)

theorem lift_objectClass (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {k : ℕ} (a : Chart B k) : lift B f (objectClass a) = f.value k a := freeMap_symbol B f a

end DiamondIntegral.Section4.RVChartRing
