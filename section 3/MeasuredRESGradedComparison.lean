import «section 3».MeasuredRESGradedSemiring
import «section 3».MeasuredRESSemiring

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

def measuredResDirectSumInvariant : PositiveGrothendieck.Invariant (measuredRESSemiringPresentation hc (M := M) S)
    (R := MeasuredRESDirectSum (M := M) hc S) where
  toFun A := measuredResDirectSumClass hc A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (MeasuredRESKPlus hc S) k) (measuredResClass_iso hc e)
  empty := by
    change DirectSum.of (MeasuredRESKPlus hc S) 0 (measuredResClass hc (MeasuredRESObject.empty S 0)) = 0
    rw [measuredResClass_empty hc, map_zero]
  unit := rfl
  product A B := measuredResDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (MeasuredRESKPlus hc S) k (measuredResClass hc a) + DirectSum.of (MeasuredRESKPlus hc S) k (measuredResClass hc b) =
        DirectSum.of (MeasuredRESKPlus hc S) k (measuredResClass hc d) + DirectSum.of (MeasuredRESKPlus hc S) k (measuredResClass hc e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (MeasuredRESKPlus hc S) k) (positiveClass_scissor (measuredRESPresentation hc S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [measuredResDirectSumClass, measuredResClass_empty hc, map_zero, add_zero]

def measuredResPresentationToDirectSum : MeasuredRESPositiveSemiring (M := M) hc S →+* MeasuredRESDirectSum hc S :=
  PositiveGrothendieck.lift (measuredRESSemiringPresentation hc S) measuredResDirectSumInvariant

@[simp] theorem measuredResPresentationToDirectSum_class {k : ℕ} (U : MeasuredRESObject (M := M) S k) :
    measuredResPresentationToDirectSum (measuredRESSemiringClass hc U) = measuredResDirectSumClass hc U :=
  PositiveGrothendieck.lift_of (measuredRESSemiringPresentation hc S)
    (measuredResDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def measuredResDirectSumToPresentationAdd : MeasuredRESDirectSum (M := M) hc S →+ MeasuredRESPositiveSemiring hc S :=
  DirectSum.toAddMonoid (fun _ => measuredRESKPlusToSemiring hc)

@[simp] theorem measuredResDirectSumToPresentationAdd_of (k : ℕ) (a : MeasuredRESKPlus (M := M) hc S k) :
    measuredResDirectSumToPresentationAdd (DirectSum.of (MeasuredRESKPlus hc S) k a) = measuredRESKPlusToSemiring hc a :=
  DirectSum.toAddMonoid_of _ _ _

theorem measuredResDirectSumToPresentationAdd_one :
    measuredResDirectSumToPresentationAdd (1 : MeasuredRESDirectSum (M := M) hc S) = 1 := by
  change measuredResDirectSumToPresentationAdd (DirectSum.of (MeasuredRESKPlus hc S) 0 (measuredResClass hc (MeasuredRESObject.unit hc S))) = 1
  rw [measuredResDirectSumToPresentationAdd_of, measuredRESKPlusToSemiring_class hc, measuredRESSemiringClass_unit hc]

theorem measuredResDirectSumToPresentationAdd_mul (a b : MeasuredRESDirectSum (M := M) hc S) :
    measuredResDirectSumToPresentationAdd (a * b) =
      measuredResDirectSumToPresentationAdd a * measuredResDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := measuredResClass_surjective hc a
      obtain ⟨V, rfl⟩ := measuredResClass_surjective hc b
      rw [DirectSum.of_mul_of]
      change measuredResDirectSumToPresentationAdd
        (DirectSum.of (MeasuredRESKPlus hc S) (i + j) (measuredResClassMul (measuredResClass hc U) (measuredResClass hc V))) = _
      rw [measuredResClassMul_class, measuredResDirectSumToPresentationAdd_of,
        measuredResDirectSumToPresentationAdd_of, measuredResDirectSumToPresentationAdd_of,
        measuredRESKPlusToSemiring_class hc, measuredRESKPlusToSemiring_class hc, measuredRESKPlusToSemiring_class hc,
        measuredRESSemiringClass_product hc]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def measuredResDirectSumToPresentation : MeasuredRESDirectSum (M := M) hc S →+* MeasuredRESPositiveSemiring hc S where
  __ := measuredResDirectSumToPresentationAdd
  map_one' := measuredResDirectSumToPresentationAdd_one
  map_mul' := measuredResDirectSumToPresentationAdd_mul

@[simp] theorem measuredResDirectSumToPresentation_class {k : ℕ} (U : MeasuredRESObject (M := M) S k) :
    measuredResDirectSumToPresentation (measuredResDirectSumClass hc U) = measuredRESSemiringClass hc U :=
  (measuredResDirectSumToPresentationAdd_of k (measuredResClass hc U)).trans (measuredRESKPlusToSemiring_class hc U)

def measuredResSemiringEquivDirectSum : MeasuredRESPositiveSemiring (M := M) hc S ≃+* MeasuredRESDirectSum hc S := by
  let F := measuredResPresentationToDirectSum (M := M) (S := S) (hc := hc)
  let B := measuredResDirectSumToPresentation (M := M) (S := S) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (measuredRESSemiringPresentation hc S)
    rintro ⟨k, U⟩
    change B (F (measuredRESSemiringClass hc U)) = measuredRESSemiringClass hc U
    rw [measuredResPresentationToDirectSum_class, measuredResDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := measuredResClass_surjective hc a
      change F (B (measuredResDirectSumClass hc U)) = measuredResDirectSumClass hc U
      rw [measuredResDirectSumToPresentation_class, measuredResPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
