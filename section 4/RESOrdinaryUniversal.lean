import «section 4».RESOrdinaryRing

/-! The universal property of the ordinary RES chart presentation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESOrdinaryRing
open RVMeasuredCharts RVMeasuredProductProperties
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Invariant (B : Base (M := M)) (R : Type*) [CommRing R] where
  value : ∀ k, RESChart B k → R
  unit : value 0 (RESChartRing.unit B) = 1
  product : ∀ k l (a : RESChart B k) (b : RESChart B l), value (l + k) (resProduct a b) = value k a * value l b
  iso : ∀ k (a b : RESChart B k) (_F : RVForgetScissors.UnderlyingIso a.toChart b.toChart), value k a = value k b
  empty : ∀ k (a : RESChart B k), a.domain = ∅ → value k a = 0
  scissor : ∀ k (a b c d : RESChart B k), RVForgetScissors.Scissor a.toChart b.toChart c.toChart d.toChart →
    value k c + value k d = value k a + value k b

def freeMap (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R) :
    FreeCommRing (Generator B) →+* R := FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_symbol (B : Base (M := M)) {R : Type*} [CommRing R] (f : Invariant B R)
    {k : ℕ} (a : RESChart B k) : freeMap B f (symbol a) = f.value k a := FreeCommRing.lift_of _ _

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
    {k : ℕ} (a : RESChart B k) : lift B f (objectClass a) = f.value k a := freeMap_symbol B f a


theorem hom_ext (B : Base (M := M)) {R : Type*} [CommRing R]
    (f g : Ring B →+* R) (h : ∀ k (a : RESChart B k), f (objectClass a) = g (objectClass a)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply FreeCommRing.hom_ext
  intro a
  exact h a.1 a.2

end DiamondIntegral.Section4.RESOrdinaryRing
