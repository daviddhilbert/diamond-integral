import Mathlib.CategoryTheory.Skeletal
import Mathlib.Algebra.Group.Defs

/-! Isomorphism classes form an additive commutative monoid whenever
actual disjoint unions have the usual isomorphisms. No cancellation is used. -/
set_option autoImplicit false
open CategoryTheory
noncomputable section
namespace DiamondIntegral.Section3
universe u v
variable {C : Type u} [Category.{v} C]

structure CoproductIsoData (C : Type u) [Category.{v} C] where
  empty : C
  coprod : C → C → C
  mapIso : ∀ {A A' B B' : C}, (A ≅ A') → (B ≅ B') → (coprod A B ≅ coprod A' B')
  assocIso : ∀ A B D, coprod (coprod A B) D ≅ coprod A (coprod B D)
  commIso : ∀ A B, coprod A B ≅ coprod B A
  emptyIso : ∀ A, coprod empty A ≅ A

@[ext] structure CoproductIsoClasses (D : CoproductIsoData C) where
  val : Quotient (isIsomorphicSetoid C)

def coproductIsoClass (D : CoproductIsoData C) (A : C) : CoproductIsoClasses D := ⟨⟦A⟧⟩

theorem coproductIsoClass_eq_iff (D : CoproductIsoData C) {A B : C} :
    coproductIsoClass D A = coproductIsoClass D B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    exact Quotient.exact (congrArg CoproductIsoClasses.val h)
  · intro h
    exact congrArg CoproductIsoClasses.mk (Quotient.sound h)

instance coproductIsoClassesZero (D : CoproductIsoData C) : Zero (CoproductIsoClasses D) := ⟨coproductIsoClass D D.empty⟩

instance coproductIsoClassesAdd (D : CoproductIsoData C) : Add (CoproductIsoClasses D) := ⟨fun a b => ⟨
  Quotient.map₂ (sa := isIsomorphicSetoid C) (sb := isIsomorphicSetoid C) (sc := isIsomorphicSetoid C) D.coprod (fun {_ _} ⟨e⟩ {_ _} ⟨f⟩ => ⟨D.mapIso e f⟩) a.val b.val⟩⟩

theorem coproductIsoClass_coprod (D : CoproductIsoData C) (A B : C) :
    coproductIsoClass D (D.coprod A B) = coproductIsoClass D A + coproductIsoClass D B := rfl

instance coproductIsoClassesAddCommMonoid (D : CoproductIsoData C) : AddCommMonoid (CoproductIsoClasses D) where
  add := (· + ·)
  zero := 0
  add_assoc a b c := by
    cases a with | mk a =>
      cases b with | mk b =>
        cases c with | mk c =>
          induction a using Quotient.inductionOn with | h A =>
            induction b using Quotient.inductionOn with | h B =>
              induction c using Quotient.inductionOn with | h E =>
                exact (coproductIsoClass_eq_iff D).mpr ⟨D.assocIso A B E⟩
  zero_add a := by
    cases a with | mk a =>
      induction a using Quotient.inductionOn with | h A =>
        exact (coproductIsoClass_eq_iff D).mpr ⟨D.emptyIso A⟩
  add_zero a := by
    cases a with | mk a =>
      induction a using Quotient.inductionOn with | h A =>
        exact (coproductIsoClass_eq_iff D).mpr ⟨(D.commIso A D.empty).trans (D.emptyIso A)⟩
  add_comm a b := by
    cases a with | mk a =>
      cases b with | mk b =>
        induction a using Quotient.inductionOn with | h A =>
          induction b using Quotient.inductionOn with | h B =>
            exact (coproductIsoClass_eq_iff D).mpr ⟨D.commIso A B⟩
  nsmul := nsmulRec

end DiamondIntegral.Section3
