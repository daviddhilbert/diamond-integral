import «section 4».RVChartRing
import «section 4».RVForgetScissors
import «section 4».RVWeightScaling

/-! The actual ordinary RV chart ring: original-base underlying
bijections and scissors ignore volume forms, while proper finite-fibre
coordinate maps and their grades are retained. The actual measured-to-
ordinary forgetful ring map is constructed. Category identification and
global Euler descent remain separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryRing
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVForgetScissors

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Generator (B : Base (M := M)) := RVChartRing.Generator B

def symbol {B : Base (M := M)} {k : ℕ} (a : Chart B k) : FreeCommRing (Generator B) := RVChartRing.symbol a

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (RVChartRing.unit B) - 1)
  | product {k l : ℕ} (a : Chart B k) (b : Chart B l) :
      Relation B (symbol (product a b) - symbol a * symbol b)
  | iso {k : ℕ} (a b : Chart B k) (F : UnderlyingIso a b) : Relation B (symbol a - symbol b)
  | empty {k : ℕ} (a : Chart B k) (h : a.domain = ∅) : Relation B (symbol a)
  | scissor {k : ℕ} (a b c d : Chart B k) (h : RVForgetScissors.Scissor a b c d) :
      Relation B (symbol c + symbol d - symbol a - symbol b)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}

def Ring (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} {k : ℕ} (a : Chart B k) : Ring B :=
  Ideal.Quotient.mk (relationIdeal B) (symbol a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit (B : Base (M := M)) : objectClass (RVChartRing.unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product {B : Base (M := M)} {k l : ℕ} (a : Chart B k) (b : Chart B l) :
    objectClass (product a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : UnderlyingIso a b) :
    objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) :
    objectClass a = 0 := relation_zero B _ (Relation.empty a ha)

theorem objectClass_scissor {B : Base (M := M)} {k : ℕ} (a b c d : Chart B k)
    (h : RVForgetScissors.Scissor a b c d) :
    objectClass c + objectClass d = objectClass a + objectClass b := by
  have hr := relation_zero B _ (Relation.scissor a b c d h)
  rw [map_sub, map_sub, map_add, sub_sub] at hr
  exact sub_eq_zero.mp hr

def forgetInvariant (B : Base (M := M)) : RVChartRing.Invariant B (Ring B) where
  value _ a := objectClass a
  unit := objectClass_unit B
  product _ _ a b := objectClass_product a b
  iso _ _a _b F := objectClass_iso (ofMeasured F)
  empty _ a ha := objectClass_empty a ha
  scissor _ a b c d h := objectClass_scissor a b c d (measured_scissor _ _ _ _ h)

def forget (B : Base (M := M)) : RVChartRing.Ring B →+* Ring B := RVChartRing.lift B (forgetInvariant B)

theorem forget_objectClass (B : Base (M := M)) {k : ℕ} (a : Chart B k) :
    forget B (RVChartRing.objectClass a) = objectClass a := RVChartRing.lift_objectClass B (forgetInvariant B) a

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : ∀ k, Chart B k → R
  unit : value 0 (RVChartRing.unit B) = 1
  product : ∀ k l (a : Chart B k) (b : Chart B l), value (l + k) (product a b) = value k a * value l b
  iso : ∀ k (a b : Chart B k) (_F : RVForgetScissors.UnderlyingIso a b), value k a = value k b
  empty : ∀ k (a : Chart B k), a.domain = ∅ → value k a = 0
  scissor : ∀ k (a b c d : Chart B k), RVForgetScissors.Scissor a b c d →
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


theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : Ring B →+* R) (h : ∀ k (a : Chart B k), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2


end DiamondIntegral.Section4.RVOrdinaryRing
