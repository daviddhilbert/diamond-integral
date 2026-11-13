import «section 4».RVAdmissibleDisjointInvariants

/-! The intrinsic disjoint-union ring of an actual admissible RV family.
Only objects in that family generate the ring. The verified partition
argument supplies all weighted scissor relations inside the family. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVFamilyDisjointPresentation
open RVMeasuredCharts RVAdmissibleFamilies
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Object {B : Base (M := M)} (F : Family B) (k : ℕ) := {a : Chart B k // F.good k a}
abbrev Generator {B : Base (M := M)} (F : Family B) := Σ k, Object F k

def unit {B : Base (M := M)} (F : Family B) : Object F 0 := ⟨RVChartRing.unit B, F.unit⟩
def product {B : Base (M := M)} (F : Family B) {k l : ℕ} (a : Object F k) (b : Object F l) : Object F (l + k) :=
  ⟨RVMeasuredProduct.product a.val b.val, F.product k l a.val b.val a.property b.property⟩
def coproduct {B : Base (M := M)} (F : Family B) {k : ℕ} (a b : Object F k) : Object F k :=
  ⟨RVTaggedCoproduct.coproduct a.val b.val, F.coproduct k a.val b.val a.property b.property⟩

def symbol {B : Base (M := M)} (F : Family B) {k : ℕ} (a : Object F k) : FreeCommRing (Generator F) := FreeCommRing.of ⟨k, a⟩

inductive Relation {B : Base (M := M)} (F : Family B) : FreeCommRing (Generator F) → Prop where
  | unit : Relation F (symbol F (unit F) - 1)
  | product {k l : ℕ} (a : Object F k) (b : Object F l) :
      Relation F (symbol F (product F a b) - symbol F a * symbol F b)
  | iso {k : ℕ} (a b : Object F k) (f : Iso a.val b.val) : Relation F (symbol F a - symbol F b)
  | empty {k : ℕ} (a : Object F k) (ha : a.val.domain = ∅) : Relation F (symbol F a)
  | coproduct {k : ℕ} (a b : Object F k) : Relation F (symbol F (coproduct F a b) - symbol F a - symbol F b)

def relationIdeal {B : Base (M := M)} (F : Family B) : Ideal (FreeCommRing (Generator F)) := Ideal.span {r | Relation F r}

def Ring {B : Base (M := M)} (F : Family B) := FreeCommRing (Generator F) ⧸ relationIdeal F
  deriving CommRing

def objectClass {B : Base (M := M)} (F : Family B) {k : ℕ} (a : Object F k) : Ring F :=
  Ideal.Quotient.mk (relationIdeal F) (symbol F a)

theorem relation_zero {B : Base (M := M)} (F : Family B) (r : FreeCommRing (Generator F)) (hr : Relation F r) :
    Ideal.Quotient.mk (relationIdeal F) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit {B : Base (M := M)} (F : Family B) : objectClass F (unit F) = 1 := by
  have h := relation_zero F _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product {B : Base (M := M)} (F : Family B) {k l : ℕ} (a : Object F k) (b : Object F l) :
    objectClass F (product F a b) = objectClass F a * objectClass F b := by
  have h := relation_zero F _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} (F : Family B) {k : ℕ} {a b : Object F k} (f : Iso a.val b.val) :
    objectClass F a = objectClass F b := by
  have h := relation_zero F _ (Relation.iso a b f)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} (F : Family B) {k : ℕ} (a : Object F k) (ha : a.val.domain = ∅) :
    objectClass F a = 0 := relation_zero F _ (Relation.empty a ha)

theorem objectClass_coproduct {B : Base (M := M)} (F : Family B) {k : ℕ} (a b : Object F k) :
    objectClass F (coproduct F a b) = objectClass F a + objectClass F b := by
  have h := relation_zero F _ (Relation.coproduct a b)
  rw [map_sub, map_sub, sub_sub] at h
  exact sub_eq_zero.mp h

structure Invariant {B : Base (M := M)} (F : Family B) (R : Type*) [CommRing R]
    extends RVAdmissibleDisjointInvariants.AdditiveInvariant F R where
  unit : value 0 (RVChartRing.unit B) F.unit = 1
  product : ∀ k l (a : Chart B k) (b : Chart B l) (ha : F.good k a) (hb : F.good l b),
    value (l + k) (RVMeasuredProduct.product a b) (F.product k l a b ha hb) = value k a ha * value l b hb
  empty : ∀ k (a : Chart B k) (ha : F.good k a), a.domain = ∅ → value k a ha = 0

def freeMap {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R] (f : Invariant F R) : FreeCommRing (Generator F) →+* R :=
  FreeCommRing.lift (fun a => f.value a.1 a.2.val a.2.property)

theorem freeMap_symbol {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R] (f : Invariant F R)
    {k : ℕ} (a : Object F k) : freeMap F f (symbol F a) = f.value k a.val a.property := FreeCommRing.lift_of _ _

theorem invariant_relation_zero {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R] (f : Invariant F R)
    (r : FreeCommRing (Generator F)) (hr : Relation F r) : freeMap F f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol]; exact sub_eq_zero.mpr f.unit
  | product a b =>
    rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol]
    exact sub_eq_zero.mpr (f.product _ _ a.val b.val a.property b.property)
  | iso a b g =>
    rw [map_sub, freeMap_symbol, freeMap_symbol]
    exact sub_eq_zero.mpr (f.iso _ a.val b.val a.property b.property g)
  | empty a ha => rw [freeMap_symbol]; exact f.empty _ a.val a.property ha
  | coproduct a b =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (f.coproduct _ a.val b.val a.property b.property)

def lift {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R] (f : Invariant F R) : Ring F →+* R :=
  Ideal.Quotient.lift _ (freeMap F f) (by
    have hle : relationIdeal F ≤ RingHom.ker (freeMap F f) := by
      apply Ideal.span_le.mpr
      intro r hr
      exact invariant_relation_zero F f r hr
    intro r hr
    exact hle hr)

theorem lift_objectClass {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R] (f : Invariant F R)
    {k : ℕ} (a : Object F k) : lift F f (objectClass F a) = f.value k a.val a.property := freeMap_symbol F f a

theorem hom_ext {B : Base (M := M)} (F : Family B) {R : Type*} [CommRing R]
    (f g : Ring F →+* R) (h : ∀ k (a : Object F k), f (objectClass F a) = g (objectClass F a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

def classInvariant {B : Base (M := M)} (F : Family B) : Invariant F (Ring F) where
  value _ a ha := objectClass F ⟨a, ha⟩
  unit := objectClass_unit F
  product _ _ a b ha hb := objectClass_product F (⟨a, ha⟩ : Object F _) (⟨b, hb⟩ : Object F _)
  iso _ a b ha hb g := objectClass_iso F (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) g
  empty _ a ha h := objectClass_empty F (⟨a, ha⟩ : Object F _) h
  coproduct _ a b ha hb := objectClass_coproduct F (⟨a, ha⟩ : Object F _) (⟨b, hb⟩ : Object F _)

theorem objectClass_scissor {B : Base (M := M)} (F : Family B) {k : ℕ} (a b c d : Object F k)
    (h : RVMeasuredGroup.Scissor a.val b.val c.val d.val) :
    objectClass F c + objectClass F d = objectClass F a + objectClass F b :=
  RVAdmissibleDisjointInvariants.scissor F (classInvariant F).toAdditiveInvariant
    a.val b.val c.val d.val a.property b.property c.property d.property h

end DiamondIntegral.Section4.RVFamilyDisjointPresentation
