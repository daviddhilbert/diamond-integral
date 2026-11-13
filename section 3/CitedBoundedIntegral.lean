import «section 3».CitedUnmeasuredIntegral
import «section 3».RVFiltration
import «section 3».VFFiltration
import «section 3».QuotientIntegral

/-! The bounded unmeasured comparison from the accepted [18], Proposition
6.18 and the bounded-degree discussion preceding Theorem 6.19. The input
uses actual finite direct sums, the restriction of the elementary special
congruence, and the original-base object lift. All consequences retain the
small VF-generated real-base specialization of CitedUnmeasuredIntegral. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

structure YinBoundedUnmeasuredLiftInput
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (B : Section2.VFGeneratedFieldBase C.base) where
  lift : ∀ k, RVBoundedPositive (M := M) (C.base : Set M) k →+ VFKPlus (C.base : Set M) k
  lift_class : ∀ k (i : Fin (k + 1)) (U : RVObject (M := M) (C.base : Set M) i.val),
    lift k (rvBoundedClass i U) = vfClass ((objectLiftVF U).raise (Nat.le_of_lt_succ i.isLt))
  surjective : ∀ k, Function.Surjective (lift k)
  kernel : ∀ k, rvBoundedSpecialCongruence (S := (C.base : Set M)) (k := k) hc = AddCon.ker (lift k)

variable {C hc hv} {B : Section2.VFGeneratedFieldBase C.base}

def boundedUnmeasuredIntegral (H : YinBoundedUnmeasuredLiftInput C hc hv B) (k : ℕ) :
    VFKPlus (M := M) (C.base : Set M) k ≃+
      (rvBoundedSpecialCongruence (S := (C.base : Set M)) (k := k) hc).Quotient :=
  integralFromKernel (H.lift k) (H.surjective k) _ (H.kernel k)

theorem boundedUnmeasuredIntegral_characterization
    (H : YinBoundedUnmeasuredLiftInput C hc hv B) (k : ℕ)
    (A : VFObject (M := M) (C.base : Set M) k) (i : Fin (k + 1))
    (U : RVObject (M := M) (C.base : Set M) i.val) :
    boundedUnmeasuredIntegral H k (vfClass A) =
      (rvBoundedSpecialCongruence (S := (C.base : Set M)) (k := k) hc).mk' (rvBoundedClass i U) ↔
      vfClass A = vfClass ((objectLiftVF U).raise (Nat.le_of_lt_succ i.isLt)) := by
  rw [boundedUnmeasuredIntegral, integralFromKernel_characterization, H.lift_class]

theorem boundedLift_transition (H : YinBoundedUnmeasuredLiftInput C hc hv B)
    {k l : ℕ} (hkl : k ≤ l) (a : RVBoundedPositive (M := M) (C.base : Set M) k) :
    H.lift l (rvBoundedTransition hkl a) = vfRaiseKPlus hkl (H.lift k a) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of i a =>
    obtain ⟨U, rfl⟩ := rvClass_surjective a
    change H.lift l (rvBoundedTransition hkl (rvBoundedClass i U)) =
      vfRaiseKPlus hkl (H.lift k (rvBoundedClass i U))
    rw [show rvBoundedTransition hkl (rvBoundedClass i U) =
      rvBoundedClass ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right hkl 1)⟩ U from
        rvBoundedTransition_of hkl i (rvClass U)]
    rw [H.lift_class, H.lift_class, vfRaiseKPlus_class]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]

@[simp] theorem boundedUnmeasuredIntegral_lift (H : YinBoundedUnmeasuredLiftInput C hc hv B)
    (k : ℕ) (a : RVBoundedPositive (M := M) (C.base : Set M) k) :
    boundedUnmeasuredIntegral H k (H.lift k a) =
      (rvBoundedSpecialCongruence (S := (C.base : Set M)) hc).mk' a :=
  (integralFromKernel_characterization (H.lift k) (H.surjective k) _ (H.kernel k) (H.lift k a) a).mpr rfl

theorem boundedUnmeasuredIntegral_transition (H : YinBoundedUnmeasuredLiftInput C hc hv B)
    {k l : ℕ} (hkl : k ≤ l) (a : VFKPlus (M := M) (C.base : Set M) k) :
    rvBoundedQuotientTransition hc hkl (boundedUnmeasuredIntegral H k a) =
      boundedUnmeasuredIntegral H l (vfRaiseKPlus hkl a) := by
  obtain ⟨b, rfl⟩ := H.surjective k a
  rw [boundedUnmeasuredIntegral_lift, rvBoundedQuotientTransition_mk,
    ← boundedLift_transition H hkl b, boundedUnmeasuredIntegral_lift]

end DiamondIntegral.Section3
