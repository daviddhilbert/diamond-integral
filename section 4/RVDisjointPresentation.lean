import «section 4».RVDisjointInvariants
import «section 4».RVGrading

/-! The actual measured RV object ring presented by measured isomorphisms,
products and tagged disjoint unions is ring-isomorphic to the weighted
scissor presentation. Both maps preserve every actual object class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDisjointPresentation
open RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Generator (B : Base (M := M)) := RVChartRing.Generator B
abbrev symbol {B : Base (M := M)} {k : ℕ} (a : Chart B k) := RVChartRing.symbol a

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (RVChartRing.unit B) - 1)
  | product {k l : ℕ} (a : Chart B k) (b : Chart B l) :
      Relation B (symbol (RVMeasuredProduct.product a b) - symbol a * symbol b)
  | iso {k : ℕ} (a b : Chart B k) (F : Iso a b) : Relation B (symbol a - symbol b)
  | empty {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) : Relation B (symbol a)
  | coproduct {k : ℕ} (a b : Chart B k) :
      Relation B (symbol (RVTaggedCoproduct.coproduct a b) - symbol a - symbol b)

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
    objectClass (RVMeasuredProduct.product a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {B : Base (M := M)} {k : ℕ} {a b : Chart B k} (F : Iso a b) : objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : a.domain = ∅) : objectClass a = 0 :=
  relation_zero B _ (Relation.empty a ha)

theorem objectClass_coproduct {B : Base (M := M)} {k : ℕ} (a b : Chart B k) :
    objectClass (RVTaggedCoproduct.coproduct a b) = objectClass a + objectClass b := by
  have h := relation_zero B _ (Relation.coproduct a b)
  rw [map_sub, map_sub, sub_sub] at h
  exact sub_eq_zero.mp h

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] extends RVDisjointInvariants.AdditiveInvariant B R where
  unit : value 0 (RVChartRing.unit B) = 1
  product : ∀ k l (a : Chart B k) (b : Chart B l),
    value (l + k) (RVMeasuredProduct.product a b) = value k a * value l b
  empty : ∀ k (a : Chart B k), a.domain = ∅ → value k a = 0

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : FreeCommRing (Generator B) →+* R :=
  FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) {k : ℕ} (a : Chart B k) :
    freeMap B f (symbol a) = f.value k a := FreeCommRing.lift_of _ _

theorem invariant_relation_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (r : FreeCommRing (Generator B)) (hr : Relation B r) : freeMap B f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, f.unit, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.product, sub_self]
  | iso a b F => rw [map_sub, freeMap_symbol, freeMap_symbol, f.iso _ a b F, sub_self]
  | empty a ha => rw [freeMap_symbol, f.empty _ a ha]
  | coproduct a b =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (f.coproduct _ a b)

def lift (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : Ring B →+* R :=
  Ideal.Quotient.lift _ (freeMap B f) (by
    have hle : relationIdeal B ≤ RingHom.ker (freeMap B f) := by
      apply Ideal.span_le.mpr
      intro r hr
      exact invariant_relation_zero B f r hr
    intro r hr
    exact hle hr)

theorem lift_objectClass (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) {k : ℕ} (a : Chart B k) :
    lift B f (objectClass a) = f.value k a := freeMap_symbol B f a

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R] (f g : Ring B →+* R)
    (h : ∀ k (a : Chart B k), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

def chartInvariant (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : RVChartRing.Invariant B R where
  value := f.value
  unit := f.unit
  product := f.product
  iso := f.iso
  empty := f.empty
  scissor _ a b c d h := RVDisjointInvariants.scissor f.toAdditiveInvariant a b c d h

def classInvariant (B : Base (M := M)) : Invariant B (Ring B) where
  value _ a := objectClass a
  unit := objectClass_unit B
  product _ _ a b := objectClass_product a b
  iso _ _ _ F := objectClass_iso F
  empty _ a ha := objectClass_empty a ha
  coproduct _ a b := objectClass_coproduct a b

def toChartInvariant (B : Base (M := M)) : Invariant B (RVChartRing.Ring B) where
  value _ a := RVChartRing.objectClass a
  unit := RVChartRing.objectClass_unit B
  product _ _ a b := RVChartRing.objectClass_product a b
  iso _ _ _ F := RVChartRing.objectClass_iso F
  empty _ a ha := RVChartRing.objectClass_empty a ha
  coproduct _ a b := RVTaggedCoproduct.class_coproduct a b

def toChartRing (B : Base (M := M)) : Ring B →+* RVChartRing.Ring B := lift B (toChartInvariant B)
def fromChartRing (B : Base (M := M)) : RVChartRing.Ring B →+* Ring B := RVChartRing.lift B (chartInvariant B (classInvariant B))

theorem toChartRing_class (B : Base (M := M)) {k : ℕ} (a : Chart B k) :
    toChartRing B (objectClass a) = RVChartRing.objectClass a := lift_objectClass B (toChartInvariant B) a

theorem fromChartRing_class (B : Base (M := M)) {k : ℕ} (a : Chart B k) :
    fromChartRing B (RVChartRing.objectClass a) = objectClass a := RVChartRing.lift_objectClass B (chartInvariant B (classInvariant B)) a

theorem to_from (B : Base (M := M)) : (toChartRing B).comp (fromChartRing B) = RingHom.id _ := by
  apply RVGrading.hom_ext B
  intro k a
  change toChartRing B (fromChartRing B (RVChartRing.objectClass a)) = RVChartRing.objectClass a
  rw [fromChartRing_class, toChartRing_class]

theorem from_to (B : Base (M := M)) : (fromChartRing B).comp (toChartRing B) = RingHom.id _ := by
  apply hom_ext B
  intro k a
  change fromChartRing B (toChartRing B (objectClass a)) = objectClass a
  rw [toChartRing_class, fromChartRing_class]

def equivalence (B : Base (M := M)) : Ring B ≃+* RVChartRing.Ring B :=
  RingEquiv.ofBijective (toChartRing B) ⟨(by
    intro x y h
    have he := congrArg (fromChartRing B) h
    exact (RingHom.congr_fun (from_to B) x).symm.trans (he.trans (RingHom.congr_fun (from_to B) y))), (by
    intro y
    exact ⟨fromChartRing B y, RingHom.congr_fun (to_from B) y⟩)⟩

end DiamondIntegral.Section4.RVDisjointPresentation
