import «section 4».GammaOrdinaryFiniteCharts
import «section 4».GammaFiniteRVPresentation

/-! The actual ordinary finite Gamma chart ring, with RV-contracted bijections
and ordinary domain scissors. Volume forms are not part of its objects.
The measured forgetful map is constructed and is surjective. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFiniteRing
open GammaOrdinaryCharts GammaOrdinaryFiniteCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Generator (B : Base (M := M)) := Σ n, FiniteChart B n

def symbol {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : FreeCommRing (Generator B) := FreeCommRing.of ⟨n, a⟩
def Scissor {B : Base (M := M)} {n : ℕ} (a b c d : FiniteChart B n) : Prop :=
  c.support = a.support ∪ b.support ∧ d.support = a.support ∩ b.support

inductive Relation (B : Base (M := M)) : FreeCommRing (Generator B) → Prop where
  | unit : Relation B (symbol (GammaOrdinaryFiniteCharts.unit B) - 1)
  | product {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) : Relation B (symbol (product a b) - symbol a * symbol b)
  | iso {n : ℕ} (a b : FiniteChart B n) (f : GammaOrdinaryCharts.Iso a.toChart b.toChart) : Relation B (symbol a - symbol b)
  | empty {n : ℕ} (a : FiniteChart B n) (ha : a.support = ∅) : Relation B (symbol a)
  | scissor {n : ℕ} (a b c d : FiniteChart B n) (h : Scissor a b c d) : Relation B (symbol c + symbol d - symbol a - symbol b)

def relationIdeal (B : Base (M := M)) : Ideal (FreeCommRing (Generator B)) := Ideal.span {r | Relation B r}
def Ring (B : Base (M := M)) := FreeCommRing (Generator B) ⧸ relationIdeal B
  deriving CommRing

def objectClass {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : Ring B := Ideal.Quotient.mk _ (symbol a)

theorem relation_zero (B : Base (M := M)) (r : FreeCommRing (Generator B)) (hr : Relation B r) :
    Ideal.Quotient.mk (relationIdeal B) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem class_unit (B : Base (M := M)) : objectClass (GammaOrdinaryFiniteCharts.unit B) = 1 := by
  have h := relation_zero B _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem class_product {B : Base (M := M)} {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) : objectClass (product a b) = objectClass a * objectClass b := by
  have h := relation_zero B _ (Relation.product a b)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem class_iso {B : Base (M := M)} {n : ℕ} {a b : FiniteChart B n} (f : GammaOrdinaryCharts.Iso a.toChart b.toChart) : objectClass a = objectClass b := by
  have h := relation_zero B _ (Relation.iso a b f)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem class_empty {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) (ha : a.support = ∅) : objectClass a = 0 :=
  relation_zero B _ (Relation.empty a ha)

theorem class_scissor {B : Base (M := M)} {n : ℕ} (a b c d : FiniteChart B n) (h : Scissor a b c d) :
    objectClass c + objectClass d = objectClass a + objectClass b := by
  have hh := relation_zero B _ (Relation.scissor a b c d h)
  rw [map_sub, map_sub, map_add, sub_sub] at hh
  exact sub_eq_zero.mp hh

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : ∀ n, FiniteChart B n → R
  unit : value 0 (GammaOrdinaryFiniteCharts.unit B) = 1
  product : ∀ n m (a : FiniteChart B m) (b : FiniteChart B n), value (n + m) (GammaOrdinaryFiniteCharts.product a b) = value m a * value n b
  iso : ∀ n (a b : FiniteChart B n), GammaOrdinaryCharts.Iso a.toChart b.toChart → value n a = value n b
  empty : ∀ n (a : FiniteChart B n), a.support = ∅ → value n a = 0
  scissor : ∀ n (a b c d : FiniteChart B n), Scissor a b c d → value n c + value n d = value n a + value n b

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : FreeCommRing (Generator B) →+* R :=
  FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) {n : ℕ} (a : FiniteChart B n) :
    freeMap B f (symbol a) = f.value n a := FreeCommRing.lift_of _ _

theorem freeMap_relation_zero (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    (r : FreeCommRing (Generator B)) (hr : Relation B r) : freeMap B f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_symbol, f.unit, sub_self]
  | product a b => rw [map_sub, map_mul, freeMap_symbol, freeMap_symbol, freeMap_symbol, f.product, sub_self]
  | iso a b g => rw [map_sub, freeMap_symbol, freeMap_symbol, f.iso _ a b g, sub_self]
  | empty a ha => rw [freeMap_symbol, f.empty _ a ha]
  | scissor a b c d h =>
    simp only [map_sub, map_add, freeMap_symbol, sub_sub]
    exact sub_eq_zero.mpr (f.scissor _ a b c d h)

def lift (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) : Ring B →+* R :=
  Ideal.Quotient.lift _ (freeMap B f) (by
    have hle : relationIdeal B ≤ RingHom.ker (freeMap B f) := Ideal.span_le.mpr (fun r hr => freeMap_relation_zero B f r hr)
    exact fun r hr => hle hr)

theorem lift_class (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) {n : ℕ} (a : FiniteChart B n) : lift B f (objectClass a) = f.value n a := freeMap_symbol B f a

theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R] (f g : Ring B →+* R)
    (h : ∀ n (a : FiniteChart B n), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

def forgetInvariant (B : Base (M := M)) : GammaFiniteRVPresentation.Invariant B (Ring B) where
  value _ a := objectClass (GammaOrdinaryFiniteCharts.ofMeasured a)
  unit := class_unit B
  product _ _ a b := class_product (GammaOrdinaryFiniteCharts.ofMeasured a) (GammaOrdinaryFiniteCharts.ofMeasured b)
  iso _ _ _ f := class_iso (GammaOrdinaryCharts.ofMeasured f)
  empty _ _ _ := class_empty _ rfl
  scissor _ _ _ _ _ _ _ _ _ _ _ := class_scissor _ _ _ _ ⟨rfl, rfl⟩

def forget (B : Base (M := M)) : GammaFiniteRVPresentation.ChartRing B →+* Ring B := GammaFiniteRVPresentation.lift B (forgetInvariant B)

theorem forget_class (B : Base (M := M)) {n : ℕ} (a : GammaFiniteRVCharts.FiniteChart B n) :
    forget B (GammaFiniteRVPresentation.objectClass a) = objectClass (GammaOrdinaryFiniteCharts.ofMeasured a) := GammaFiniteRVPresentation.lift_class B (forgetInvariant B) a

def weightedFreeLift (B : Base (M := M)) : FreeCommRing (Generator B) →+* GammaFiniteRVPresentation.ChartRing B :=
  FreeCommRing.lift (fun a => GammaFiniteRVPresentation.objectClass (GammaOrdinaryFiniteCharts.toWeighted a.2))

theorem forget_weightedFreeLift (B : Base (M := M)) :
    (forget B).comp (weightedFreeLift B) = Ideal.Quotient.mk (relationIdeal B) := by
  apply FreeCommRing.hom_ext
  intro a
  change forget B (weightedFreeLift B (symbol a.2)) = objectClass a.2
  have he : weightedFreeLift B (symbol a.2) = GammaFiniteRVPresentation.objectClass (GammaOrdinaryFiniteCharts.toWeighted a.2) := FreeCommRing.lift_of _ _
  rw [he]
  exact forget_class B (GammaOrdinaryFiniteCharts.toWeighted a.2)

theorem forget_surjective (B : Base (M := M)) : Function.Surjective (forget B) := by
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨weightedFreeLift B r, (RingHom.congr_fun (forget_weightedFreeLift B) r).trans hr⟩

end DiamondIntegral.Section4.GammaOrdinaryFiniteRing
