import «section 3».GammaGroundRVGenerators

/-! The bounded-degree RV positive monoids are genuine finite direct
sums. Their transition maps preserve the actual degree and their relation
is the restriction of the concrete nonhomogeneous special congruence. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l m : ℕ}

abbrev GammaGroundRVBoundedPositive (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) := DirectSum (Fin (k + 1)) (fun i => GammaGroundRVKPlus (M := M) hc ground i.val)

def gammaGroundRVBoundedClass (i : Fin (k + 1)) (U : GammaGroundRVObject (M := M) hc ground i.val) : GammaGroundRVBoundedPositive hc ground k :=
  DirectSum.of (fun i : Fin (k + 1) => GammaGroundRVKPlus hc ground i.val) i (gammaGroundRVClass U)

def gammaGroundRVBoundedInclude : GammaGroundRVBoundedPositive (M := M) hc ground k →+ GammaGroundRVPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundRVKPlusToSemiring)

@[simp] theorem gammaGroundRVBoundedInclude_of (i : Fin (k + 1)) (a : GammaGroundRVKPlus (M := M) hc ground i.val) :
    gammaGroundRVBoundedInclude (DirectSum.of (fun i : Fin (k + 1) => GammaGroundRVKPlus hc ground i.val) i a) = gammaGroundRVKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

@[simp] theorem gammaGroundRVBoundedInclude_class (i : Fin (k + 1)) (U : GammaGroundRVObject (M := M) hc ground i.val) :
    gammaGroundRVBoundedInclude (gammaGroundRVBoundedClass i U) = gammaGroundRVSemiringClass U :=
  (gammaGroundRVBoundedInclude_of i (gammaGroundRVClass U)).trans (gammaGroundRVKPlusToSemiring_class U)

def gammaGroundRVBoundedTransition (hkl : k ≤ l) : GammaGroundRVBoundedPositive (M := M) hc ground k →+ GammaGroundRVBoundedPositive hc ground l :=
  DirectSum.toAddMonoid (fun i => DirectSum.of (fun j : Fin (l + 1) => GammaGroundRVKPlus hc ground j.val)
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hkl 1)⟩)

@[simp] theorem gammaGroundRVBoundedTransition_of (hkl : k ≤ l) (i : Fin (k + 1))
    (a : GammaGroundRVKPlus (M := M) hc ground i.val) :
    gammaGroundRVBoundedTransition hkl (DirectSum.of (fun i : Fin (k + 1) => GammaGroundRVKPlus hc ground i.val) i a) =
      DirectSum.of (fun j : Fin (l + 1) => GammaGroundRVKPlus hc ground j.val)
        ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hkl 1)⟩ a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundRVBoundedInclude_transition (hkl : k ≤ l) (a : GammaGroundRVBoundedPositive (M := M) hc ground k) :
    gammaGroundRVBoundedInclude (gammaGroundRVBoundedTransition hkl a) = gammaGroundRVBoundedInclude a := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a => rw [gammaGroundRVBoundedTransition_of, gammaGroundRVBoundedInclude_of, gammaGroundRVBoundedInclude_of]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem gammaGroundRVBoundedTransition_refl :
    gammaGroundRVBoundedTransition (M := M) (hc := hc) (ground := ground) (le_refl k) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro a
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a => rw [gammaGroundRVBoundedTransition_of]; rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem gammaGroundRVBoundedTransition_comp (hkl : k ≤ l) (hlm : l ≤ m) :
    (gammaGroundRVBoundedTransition (M := M) (hc := hc) (ground := ground) hlm).comp (gammaGroundRVBoundedTransition hkl) =
      gammaGroundRVBoundedTransition (hkl.trans hlm) := by
  apply AddMonoidHom.ext
  intro a
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a =>
    rw [AddMonoidHom.comp_apply]
    rw [gammaGroundRVBoundedTransition_of, gammaGroundRVBoundedTransition_of, gammaGroundRVBoundedTransition_of]
  | add a b ha hb => simpa only [map_add, AddMonoidHom.comp_apply] using congrArg₂ (· + ·) ha hb

def gammaGroundRVBoundedSpecialHom (hc : CanonicalStructure.IsCanonical (M := M)) :
    GammaGroundRVBoundedPositive (M := M) hc ground k →+ (gammaGroundRVSpecialCongruence hc ground).Quotient :=
  (gammaGroundRVSpecialCongruence hc ground).mk'.toAddMonoidHom.comp gammaGroundRVBoundedInclude

def gammaGroundRVBoundedSpecialCongruence (hc : CanonicalStructure.IsCanonical (M := M)) :
    AddCon (GammaGroundRVBoundedPositive (M := M) hc ground k) := AddCon.ker (gammaGroundRVBoundedSpecialHom hc)

def gammaGroundRVBoundedQuotientTransition (hc : CanonicalStructure.IsCanonical (M := M)) (hkl : k ≤ l) :
    (gammaGroundRVBoundedSpecialCongruence (M := M) (ground := ground) (k := k) hc).Quotient →+
      (gammaGroundRVBoundedSpecialCongruence (M := M) (ground := ground) (k := l) hc).Quotient :=
  (gammaGroundRVBoundedSpecialCongruence hc).lift
    ((gammaGroundRVBoundedSpecialCongruence hc).mk'.comp (gammaGroundRVBoundedTransition hkl)) (by
      intro a b hab
      apply (gammaGroundRVBoundedSpecialCongruence (k := l) hc).eq.mpr
      change (gammaGroundRVSpecialCongruence hc ground).mk' (gammaGroundRVBoundedInclude (gammaGroundRVBoundedTransition hkl a)) =
        (gammaGroundRVSpecialCongruence hc ground).mk' (gammaGroundRVBoundedInclude (gammaGroundRVBoundedTransition hkl b))
      rw [gammaGroundRVBoundedInclude_transition, gammaGroundRVBoundedInclude_transition]
      exact hab)

@[simp] theorem gammaGroundRVBoundedQuotientTransition_mk
    (hc : CanonicalStructure.IsCanonical (M := M)) (hkl : k ≤ l)
    (a : GammaGroundRVBoundedPositive (M := M) hc ground k) :
    gammaGroundRVBoundedQuotientTransition hc hkl ((gammaGroundRVBoundedSpecialCongruence hc).mk' a) =
      (gammaGroundRVBoundedSpecialCongruence hc).mk' (gammaGroundRVBoundedTransition hkl a) := rfl

end DiamondIntegral.Section3
