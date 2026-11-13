import «section 3».RVGenerators

/-! The bounded-degree RV positive monoids are genuine finite direct
sums. Their transition maps preserve the actual degree and their relation
is the restriction of the concrete nonhomogeneous special congruence. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l m : ℕ}

abbrev RVBoundedPositive (S : Set M) (k : ℕ) := DirectSum (Fin (k + 1)) (fun i => RVKPlus (M := M) S i.val)

def rvBoundedClass (i : Fin (k + 1)) (U : RVObject (M := M) S i.val) : RVBoundedPositive S k :=
  DirectSum.of (fun i : Fin (k + 1) => RVKPlus S i.val) i (rvClass U)

def rvBoundedInclude : RVBoundedPositive (M := M) S k →+ RVPositiveSemiring S :=
  DirectSum.toAddMonoid (fun _ => rvKPlusToSemiring)

@[simp] theorem rvBoundedInclude_of (i : Fin (k + 1)) (a : RVKPlus (M := M) S i.val) :
    rvBoundedInclude (DirectSum.of (fun i : Fin (k + 1) => RVKPlus S i.val) i a) = rvKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

@[simp] theorem rvBoundedInclude_class (i : Fin (k + 1)) (U : RVObject (M := M) S i.val) :
    rvBoundedInclude (rvBoundedClass i U) = rvSemiringClass U :=
  (rvBoundedInclude_of i (rvClass U)).trans (rvKPlusToSemiring_class U)

def rvBoundedTransition (hkl : k ≤ l) : RVBoundedPositive (M := M) S k →+ RVBoundedPositive S l :=
  DirectSum.toAddMonoid (fun i => DirectSum.of (fun j : Fin (l + 1) => RVKPlus S j.val)
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hkl 1)⟩)

@[simp] theorem rvBoundedTransition_of (hkl : k ≤ l) (i : Fin (k + 1))
    (a : RVKPlus (M := M) S i.val) :
    rvBoundedTransition hkl (DirectSum.of (fun i : Fin (k + 1) => RVKPlus S i.val) i a) =
      DirectSum.of (fun j : Fin (l + 1) => RVKPlus S j.val)
        ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hkl 1)⟩ a :=
  DirectSum.toAddMonoid_of _ _ _

theorem rvBoundedInclude_transition (hkl : k ≤ l) (a : RVBoundedPositive (M := M) S k) :
    rvBoundedInclude (rvBoundedTransition hkl a) = rvBoundedInclude a := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a => rw [rvBoundedTransition_of, rvBoundedInclude_of, rvBoundedInclude_of]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem rvBoundedTransition_refl :
    rvBoundedTransition (M := M) (S := S) (le_refl k) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro a
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a => rw [rvBoundedTransition_of]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem rvBoundedTransition_comp (hkl : k ≤ l) (hlm : l ≤ m) :
    (rvBoundedTransition (M := M) (S := S) hlm).comp (rvBoundedTransition hkl) =
      rvBoundedTransition (hkl.trans hlm) := by
  apply AddMonoidHom.ext
  intro a
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a =>
    rw [AddMonoidHom.comp_apply]
    rw [rvBoundedTransition_of, rvBoundedTransition_of, rvBoundedTransition_of]
  | add a b ha hb => simpa only [map_add, AddMonoidHom.comp_apply] using congrArg₂ (· + ·) ha hb

def rvBoundedSpecialHom (hc : CanonicalStructure.IsCanonical (M := M)) :
    RVBoundedPositive (M := M) S k →+ (rvSpecialCongruence hc S).Quotient :=
  (rvSpecialCongruence hc S).mk'.toAddMonoidHom.comp rvBoundedInclude

def rvBoundedSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M)) :
    AddCon (RVBoundedPositive (M := M) S k) := AddCon.ker (rvBoundedSpecialHom hc)

def rvBoundedQuotientTransition (hc : CanonicalStructure.IsCanonical (M := M)) (hkl : k ≤ l) :
    (rvBoundedSpecialCongruence (M := M) (S := S) (k := k) hc).Quotient →+
      (rvBoundedSpecialCongruence (M := M) (S := S) (k := l) hc).Quotient :=
  (rvBoundedSpecialCongruence hc).lift
    ((rvBoundedSpecialCongruence hc).mk'.comp (rvBoundedTransition hkl)) (by
      intro a b hab
      apply (rvBoundedSpecialCongruence (k := l) hc).eq.mpr
      change (rvSpecialCongruence hc S).mk' (rvBoundedInclude (rvBoundedTransition hkl a)) =
        (rvSpecialCongruence hc S).mk' (rvBoundedInclude (rvBoundedTransition hkl b))
      rw [rvBoundedInclude_transition, rvBoundedInclude_transition]
      exact hab)

@[simp] theorem rvBoundedQuotientTransition_mk
    (hc : CanonicalStructure.IsCanonical (M := M)) (hkl : k ≤ l)
    (a : RVBoundedPositive (M := M) S k) :
    rvBoundedQuotientTransition hc hkl ((rvBoundedSpecialCongruence hc).mk' a) =
      (rvBoundedSpecialCongruence hc).mk' (rvBoundedTransition hkl a) := rfl

end DiamondIntegral.Section3
