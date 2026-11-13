import «section 3».MeasuredFiniteGammaGradedSemiring
import «section 3».MeasuredFiniteGammaSemiring

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

def measuredFiniteGammaDirectSumInvariant : PositiveGrothendieck.Invariant (measuredFiniteGammaSemiringPresentation hc (M := M) S)
    (R := MeasuredFiniteGammaDirectSum (M := M) hc S) where
  toFun A := measuredFiniteGammaDirectSumClass A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (MeasuredFiniteGammaKPlus hc S) k) (measuredFiniteGammaClass_iso e)
  empty := by
    change DirectSum.of (MeasuredFiniteGammaKPlus hc S) 0 (measuredFiniteGammaClass (MeasuredFiniteGammaObject.empty hc S 0)) = 0
    rw [measuredFiniteGammaClass_empty, map_zero]
  unit := rfl
  product A B := measuredFiniteGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass a) + DirectSum.of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass b) =
        DirectSum.of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass d) + DirectSum.of (MeasuredFiniteGammaKPlus hc S) k (measuredFiniteGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (MeasuredFiniteGammaKPlus hc S) k) (positiveClass_scissor (measuredFiniteGammaPresentation hc S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [measuredFiniteGammaDirectSumClass, measuredFiniteGammaClass_empty, map_zero, add_zero]

def measuredFiniteGammaPresentationToDirectSum : MeasuredFiniteGammaPositiveSemiring (M := M) hc S →+* MeasuredFiniteGammaDirectSum hc S :=
  PositiveGrothendieck.lift (measuredFiniteGammaSemiringPresentation hc S) measuredFiniteGammaDirectSumInvariant

@[simp] theorem measuredFiniteGammaPresentationToDirectSum_class {k : ℕ} (U : MeasuredFiniteGammaObject (M := M) hc S k) :
    measuredFiniteGammaPresentationToDirectSum (measuredFiniteGammaSemiringClass U) = measuredFiniteGammaDirectSumClass U :=
  PositiveGrothendieck.lift_of (measuredFiniteGammaSemiringPresentation hc S)
    (measuredFiniteGammaDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def measuredFiniteGammaDirectSumToPresentationAdd : MeasuredFiniteGammaDirectSum (M := M) hc S →+ MeasuredFiniteGammaPositiveSemiring hc S :=
  DirectSum.toAddMonoid (fun _ => measuredFiniteGammaKPlusToSemiring)

@[simp] theorem measuredFiniteGammaDirectSumToPresentationAdd_of (k : ℕ) (a : MeasuredFiniteGammaKPlus (M := M) hc S k) :
    measuredFiniteGammaDirectSumToPresentationAdd (DirectSum.of (MeasuredFiniteGammaKPlus hc S) k a) = measuredFiniteGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem measuredFiniteGammaDirectSumToPresentationAdd_one :
    measuredFiniteGammaDirectSumToPresentationAdd (1 : MeasuredFiniteGammaDirectSum (M := M) hc S) = 1 := by
  change measuredFiniteGammaDirectSumToPresentationAdd (DirectSum.of (MeasuredFiniteGammaKPlus hc S) 0 (measuredFiniteGammaClass (MeasuredFiniteGammaObject.unit hc S))) = 1
  rw [measuredFiniteGammaDirectSumToPresentationAdd_of, measuredFiniteGammaKPlusToSemiring_class, measuredFiniteGammaSemiringClass_unit]

theorem measuredFiniteGammaDirectSumToPresentationAdd_mul (a b : MeasuredFiniteGammaDirectSum (M := M) hc S) :
    measuredFiniteGammaDirectSumToPresentationAdd (a * b) =
      measuredFiniteGammaDirectSumToPresentationAdd a * measuredFiniteGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := measuredFiniteGammaClass_surjective a
      obtain ⟨V, rfl⟩ := measuredFiniteGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change measuredFiniteGammaDirectSumToPresentationAdd
        (DirectSum.of (MeasuredFiniteGammaKPlus hc S) (i + j) (measuredFiniteGammaClassMul (measuredFiniteGammaClass U) (measuredFiniteGammaClass V))) = _
      rw [measuredFiniteGammaClassMul_class, measuredFiniteGammaDirectSumToPresentationAdd_of,
        measuredFiniteGammaDirectSumToPresentationAdd_of, measuredFiniteGammaDirectSumToPresentationAdd_of,
        measuredFiniteGammaKPlusToSemiring_class, measuredFiniteGammaKPlusToSemiring_class, measuredFiniteGammaKPlusToSemiring_class,
        measuredFiniteGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def measuredFiniteGammaDirectSumToPresentation : MeasuredFiniteGammaDirectSum (M := M) hc S →+* MeasuredFiniteGammaPositiveSemiring hc S where
  __ := measuredFiniteGammaDirectSumToPresentationAdd
  map_one' := measuredFiniteGammaDirectSumToPresentationAdd_one
  map_mul' := measuredFiniteGammaDirectSumToPresentationAdd_mul

@[simp] theorem measuredFiniteGammaDirectSumToPresentation_class {k : ℕ} (U : MeasuredFiniteGammaObject (M := M) hc S k) :
    measuredFiniteGammaDirectSumToPresentation (measuredFiniteGammaDirectSumClass U) = measuredFiniteGammaSemiringClass U :=
  (measuredFiniteGammaDirectSumToPresentationAdd_of k (measuredFiniteGammaClass U)).trans (measuredFiniteGammaKPlusToSemiring_class U)

def measuredFiniteGammaSemiringEquivDirectSum : MeasuredFiniteGammaPositiveSemiring (M := M) hc S ≃+* MeasuredFiniteGammaDirectSum hc S := by
  let F := measuredFiniteGammaPresentationToDirectSum (M := M) (S := S) (hc := hc)
  let B := measuredFiniteGammaDirectSumToPresentation (M := M) (S := S) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (measuredFiniteGammaSemiringPresentation hc S)
    rintro ⟨k, U⟩
    change B (F (measuredFiniteGammaSemiringClass U)) = measuredFiniteGammaSemiringClass U
    rw [measuredFiniteGammaPresentationToDirectSum_class, measuredFiniteGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := measuredFiniteGammaClass_surjective a
      change F (B (measuredFiniteGammaDirectSumClass U)) = measuredFiniteGammaDirectSumClass U
      rw [measuredFiniteGammaDirectSumToPresentation_class, measuredFiniteGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
