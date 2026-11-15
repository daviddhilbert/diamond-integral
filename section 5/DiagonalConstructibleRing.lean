import «section 5».RationalDiagonalActions
import «section 5».NormalizedGraphDescent
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The raw ring of constructible complex sets with finite diagonal
compatible-root actions. Relations use the entire constructible,
equivariant bijection graph. The geometric variety comparison is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
open Classical FirstOrder FirstOrder.Language
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

structure Object where
  arity : ℕ
  weights : Fin arity → ℚ
  domain : Set (Fin arity → ℂ)
  definable : (Set.univ : Set ℂ).Definable Language.ring domain
  invariant : RationalInvariant weights domain

structure Iso (X Y : Object) where
  equiv : X.domain ≃ Y.domain
  graph_definable : (Set.univ : Set ℂ).Definable Language.ring
    (framedEquivGraph X.domain Y.domain equiv)
  graph_invariant : RationalInvariant (Fin.append X.weights Y.weights)
    (framedEquivGraph X.domain Y.domain equiv)

def unit : Object where
  arity := 0
  weights := Fin.elim0
  domain := Set.univ
  definable := Set.definable_univ
  invariant := fun _ _ => Iff.rfl

def product (X Y : Object) : Object where
  arity := X.arity + Y.arity
  weights := Fin.append X.weights Y.weights
  domain := tupleProductSet X.domain Y.domain
  definable := (X.definable.preimage_comp (Fin.castAdd Y.arity)).inter
    (Y.definable.preimage_comp (Fin.natAdd X.arity))
  invariant := rationalInvariant_product X.weights Y.weights X.domain Y.domain X.invariant Y.invariant

def cut (X : Object) (D : Set (Fin X.arity → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hiD : RationalInvariant X.weights D) : Object where
  arity := X.arity
  weights := X.weights
  domain := X.domain ∩ D
  definable := X.definable.inter hD
  invariant η x := and_congr (X.invariant η x) (hiD η x)

def outside (X : Object) (D : Set (Fin X.arity → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hiD : RationalInvariant X.weights D) : Object where
  arity := X.arity
  weights := X.weights
  domain := X.domain \ D
  definable := X.definable.inter hD.compl
  invariant η x := and_congr (X.invariant η x) (not_congr (hiD η x))

def symbol (X : Object) : FreeCommRing Object := FreeCommRing.of X

inductive Relation : FreeCommRing Object → Prop where
  | unit : Relation (symbol unit - 1)
  | product (X Y : Object) : Relation (symbol (product X Y) - symbol X * symbol Y)
  | iso (X Y : Object) (f : Iso X Y) : Relation (symbol X - symbol Y)
  | empty (X : Object) (h : X.domain = ∅) : Relation (symbol X)
  | scissor (X : Object) (D : Set (Fin X.arity → ℂ))
      (hD : (Set.univ : Set ℂ).Definable Language.ring D)
      (hiD : RationalInvariant X.weights D) :
      Relation (symbol X - symbol (cut X D hD hiD) - symbol (outside X D hD hiD))

def relationIdeal : Ideal (FreeCommRing Object) := Ideal.span {r | Relation r}

def Ring := FreeCommRing Object ⧸ relationIdeal
  deriving CommRing

def objectClass (X : Object) : Ring := Ideal.Quotient.mk relationIdeal (symbol X)

theorem relation_zero (r : FreeCommRing Object) (hr : Relation r) :
    Ideal.Quotient.mk relationIdeal r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit : objectClass unit = 1 := by
  have h := relation_zero _ Relation.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem objectClass_product (X Y : Object) : objectClass (product X Y) = objectClass X * objectClass Y := by
  have h := relation_zero _ (Relation.product X Y)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem objectClass_iso {X Y : Object} (f : Iso X Y) : objectClass X = objectClass Y := by
  have h := relation_zero _ (Relation.iso X Y f)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem objectClass_empty (X : Object) (hX : X.domain = ∅) : objectClass X = 0 :=
  relation_zero _ (Relation.empty X hX)

theorem objectClass_scissor (X : Object) (D : Set (Fin X.arity → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hiD : RationalInvariant X.weights D) :
    objectClass X = objectClass (cut X D hD hiD) + objectClass (outside X D hD hiD) := by
  have h := relation_zero _ (Relation.scissor X D hD hiD)
  rw [map_sub, map_sub, sub_sub] at h
  exact sub_eq_zero.mp h

structure Invariant (R : Type*) [CommRing R] where
  value : Object → R
  unit : value unit = 1
  product : ∀ X Y, value (product X Y) = value X * value Y
  iso : ∀ X Y, Iso X Y → value X = value Y
  empty : ∀ X, X.domain = ∅ → value X = 0
  scissor : ∀ X D hD hiD, value X = value (cut X D hD hiD) + value (outside X D hD hiD)

def lift {R : Type*} [CommRing R] (I : Invariant R) : Ring →+* R :=
  Ideal.Quotient.lift relationIdeal (FreeCommRing.lift I.value) (by
    intro a ha
    have h : relationIdeal ≤ RingHom.ker (FreeCommRing.lift I.value) := by
      apply Ideal.span_le.mpr
      intro r hr
      change FreeCommRing.lift I.value r = 0
      cases hr with
      | unit => simpa [symbol] using sub_eq_zero.mpr I.unit
      | product X Y => simpa [symbol] using sub_eq_zero.mpr (I.product X Y)
      | iso X Y f => simpa [symbol] using sub_eq_zero.mpr (I.iso X Y f)
      | empty X h => simpa [symbol] using I.empty X h
      | scissor X D hD hiD =>
        simpa [symbol, sub_sub] using sub_eq_zero.mpr (I.scissor X D hD hiD)
    exact h ha)

theorem lift_objectClass {R : Type*} [CommRing R] (I : Invariant R) (X : Object) :
    lift I (objectClass X) = I.value X := by
  change FreeCommRing.lift I.value (FreeCommRing.of X) = _
  simp

end DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
