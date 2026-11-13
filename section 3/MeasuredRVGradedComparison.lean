import «section 3».MeasuredRVGradedSemiring
import «section 3».MeasuredRVSemiring

/-! The universal semiring presentation is exactly the direct sum of
the genuine fixed-degree positive scissors. In particular, supplying
multiplication has introduced no unintended additive identifications. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def measuredRVDirectSumInvariant : PositiveGrothendieck.Invariant (measuredRVSemiringPresentation hc (M := M) S)
    (R := MeasuredRVDirectSum (M := M) hc S) where
  toFun A := measuredRVDirectSumClass hc A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (MeasuredRVKPlus hc S) k) (measuredRVClass_iso hc e)
  empty := by
    change DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredRVObject.empty S 0)) = 0
    rw [measuredRVClass_empty hc, map_zero]
  unit := rfl
  product A B := measuredRVDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc a) + DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc b) =
        DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc d) + DirectSum.of (MeasuredRVKPlus hc S) k (measuredRVClass hc e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (MeasuredRVKPlus hc S) k) (positiveClass_scissor (measuredRVPresentation hc S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [measuredRVDirectSumClass, measuredRVClass_empty hc, map_zero, add_zero]

def measuredRVPresentationToDirectSum : MeasuredRVPositiveSemiring (M := M) hc S →+* MeasuredRVDirectSum hc S :=
  PositiveGrothendieck.lift (measuredRVSemiringPresentation hc S) measuredRVDirectSumInvariant

@[simp] theorem measuredRVPresentationToDirectSum_class {k : ℕ} (U : MeasuredRVObject (M := M) S k) :
    measuredRVPresentationToDirectSum (measuredRVSemiringClass hc U) = measuredRVDirectSumClass hc U :=
  PositiveGrothendieck.lift_of (measuredRVSemiringPresentation hc S)
    (measuredRVDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def measuredRVDirectSumToPresentationAdd : MeasuredRVDirectSum (M := M) hc S →+ MeasuredRVPositiveSemiring hc S :=
  DirectSum.toAddMonoid (fun _ => measuredRVKPlusToSemiring hc)

@[simp] theorem measuredRVDirectSumToPresentationAdd_of (k : ℕ) (a : MeasuredRVKPlus (M := M) hc S k) :
    measuredRVDirectSumToPresentationAdd (DirectSum.of (MeasuredRVKPlus hc S) k a) = measuredRVKPlusToSemiring hc a :=
  DirectSum.toAddMonoid_of _ _ _

theorem measuredRVDirectSumToPresentationAdd_one :
    measuredRVDirectSumToPresentationAdd (1 : MeasuredRVDirectSum (M := M) hc S) = 1 := by
  change measuredRVDirectSumToPresentationAdd (DirectSum.of (MeasuredRVKPlus hc S) 0 (measuredRVClass hc (MeasuredRVObject.unit hc S))) = 1
  rw [measuredRVDirectSumToPresentationAdd_of, measuredRVKPlusToSemiring_class hc, measuredRVSemiringClass_unit hc]

theorem measuredRVDirectSumToPresentationAdd_mul (a b : MeasuredRVDirectSum (M := M) hc S) :
    measuredRVDirectSumToPresentationAdd (a * b) =
      measuredRVDirectSumToPresentationAdd a * measuredRVDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
      obtain ⟨V, rfl⟩ := measuredRVClass_surjective hc b
      rw [DirectSum.of_mul_of]
      change measuredRVDirectSumToPresentationAdd
        (DirectSum.of (MeasuredRVKPlus hc S) (i + j) (measuredRVClassMul (measuredRVClass hc U) (measuredRVClass hc V))) = _
      rw [measuredRVClassMul_class, measuredRVDirectSumToPresentationAdd_of,
        measuredRVDirectSumToPresentationAdd_of, measuredRVDirectSumToPresentationAdd_of,
        measuredRVKPlusToSemiring_class hc, measuredRVKPlusToSemiring_class hc, measuredRVKPlusToSemiring_class hc,
        measuredRVSemiringClass_product hc]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def measuredRVDirectSumToPresentation : MeasuredRVDirectSum (M := M) hc S →+* MeasuredRVPositiveSemiring hc S where
  __ := measuredRVDirectSumToPresentationAdd
  map_one' := measuredRVDirectSumToPresentationAdd_one
  map_mul' := measuredRVDirectSumToPresentationAdd_mul

@[simp] theorem measuredRVDirectSumToPresentation_class {k : ℕ} (U : MeasuredRVObject (M := M) S k) :
    measuredRVDirectSumToPresentation (measuredRVDirectSumClass hc U) = measuredRVSemiringClass hc U :=
  (measuredRVDirectSumToPresentationAdd_of k (measuredRVClass hc U)).trans (measuredRVKPlusToSemiring_class hc U)

def measuredRVSemiringEquivDirectSum : MeasuredRVPositiveSemiring (M := M) hc S ≃+* MeasuredRVDirectSum hc S := by
  let F := measuredRVPresentationToDirectSum (M := M) (S := S) (hc := hc)
  let B := measuredRVDirectSumToPresentation (M := M) (S := S) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (measuredRVSemiringPresentation hc S)
    rintro ⟨k, U⟩
    change B (F (measuredRVSemiringClass hc U)) = measuredRVSemiringClass hc U
    rw [measuredRVPresentationToDirectSum_class, measuredRVDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := measuredRVClass_surjective hc a
      change F (B (measuredRVDirectSumClass hc U)) = measuredRVDirectSumClass hc U
      rw [measuredRVDirectSumToPresentation_class, measuredRVPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
