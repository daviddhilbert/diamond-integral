import «section 3».MeasuredGammaGradedSemiring
import «section 3».MeasuredGammaSemiring

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

def measuredGammaDirectSumInvariant : PositiveGrothendieck.Invariant (measuredGammaSemiringPresentation hc (M := M) S)
    (R := MeasuredGammaDirectSum (M := M) hc S) where
  toFun A := measuredGammaDirectSumClass hc A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (MeasuredGammaKPlus hc S) k) (measuredGammaClass_iso e)
  empty := by
    change DirectSum.of (MeasuredGammaKPlus hc S) 0 (measuredGammaClass (MeasuredGammaObject.empty hc S 0)) = 0
    rw [measuredGammaClass_empty, map_zero]
  unit := rfl
  product A B := measuredGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (MeasuredGammaKPlus hc S) k (measuredGammaClass a) + DirectSum.of (MeasuredGammaKPlus hc S) k (measuredGammaClass b) =
        DirectSum.of (MeasuredGammaKPlus hc S) k (measuredGammaClass d) + DirectSum.of (MeasuredGammaKPlus hc S) k (measuredGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (MeasuredGammaKPlus hc S) k) (positiveClass_scissor (measuredGammaPresentation hc S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [measuredGammaDirectSumClass, measuredGammaClass_empty, map_zero, add_zero]

def measuredGammaPresentationToDirectSum : MeasuredGammaPositiveSemiring (M := M) hc S →+* MeasuredGammaDirectSum hc S :=
  PositiveGrothendieck.lift (measuredGammaSemiringPresentation hc S) measuredGammaDirectSumInvariant

@[simp] theorem measuredGammaPresentationToDirectSum_class {k : ℕ} (U : MeasuredGammaObject (M := M) hc S k) :
    measuredGammaPresentationToDirectSum (measuredGammaSemiringClass U) = measuredGammaDirectSumClass hc U :=
  PositiveGrothendieck.lift_of (measuredGammaSemiringPresentation hc S)
    (measuredGammaDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def measuredGammaDirectSumToPresentationAdd : MeasuredGammaDirectSum (M := M) hc S →+ MeasuredGammaPositiveSemiring hc S :=
  DirectSum.toAddMonoid (fun _ => measuredGammaKPlusToSemiring)

@[simp] theorem measuredGammaDirectSumToPresentationAdd_of (k : ℕ) (a : MeasuredGammaKPlus (M := M) hc S k) :
    measuredGammaDirectSumToPresentationAdd (DirectSum.of (MeasuredGammaKPlus hc S) k a) = measuredGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem measuredGammaDirectSumToPresentationAdd_one :
    measuredGammaDirectSumToPresentationAdd (1 : MeasuredGammaDirectSum (M := M) hc S) = 1 := by
  change measuredGammaDirectSumToPresentationAdd (DirectSum.of (MeasuredGammaKPlus hc S) 0 (measuredGammaClass (MeasuredGammaObject.unit hc S))) = 1
  rw [measuredGammaDirectSumToPresentationAdd_of, measuredGammaKPlusToSemiring_class, measuredGammaSemiringClass_unit]

theorem measuredGammaDirectSumToPresentationAdd_mul (a b : MeasuredGammaDirectSum (M := M) hc S) :
    measuredGammaDirectSumToPresentationAdd (a * b) =
      measuredGammaDirectSumToPresentationAdd a * measuredGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
      obtain ⟨V, rfl⟩ := measuredGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change measuredGammaDirectSumToPresentationAdd
        (DirectSum.of (MeasuredGammaKPlus hc S) (i + j) (measuredGammaClassMul (measuredGammaClass U) (measuredGammaClass V))) = _
      rw [measuredGammaClassMul_class, measuredGammaDirectSumToPresentationAdd_of,
        measuredGammaDirectSumToPresentationAdd_of, measuredGammaDirectSumToPresentationAdd_of,
        measuredGammaKPlusToSemiring_class, measuredGammaKPlusToSemiring_class, measuredGammaKPlusToSemiring_class,
        measuredGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def measuredGammaDirectSumToPresentation : MeasuredGammaDirectSum (M := M) hc S →+* MeasuredGammaPositiveSemiring hc S where
  __ := measuredGammaDirectSumToPresentationAdd
  map_one' := measuredGammaDirectSumToPresentationAdd_one
  map_mul' := measuredGammaDirectSumToPresentationAdd_mul

@[simp] theorem measuredGammaDirectSumToPresentation_class {k : ℕ} (U : MeasuredGammaObject (M := M) hc S k) :
    measuredGammaDirectSumToPresentation (measuredGammaDirectSumClass hc U) = measuredGammaSemiringClass U :=
  (measuredGammaDirectSumToPresentationAdd_of k (measuredGammaClass U)).trans (measuredGammaKPlusToSemiring_class U)

def measuredGammaSemiringEquivDirectSum : MeasuredGammaPositiveSemiring (M := M) hc S ≃+* MeasuredGammaDirectSum hc S := by
  let F := measuredGammaPresentationToDirectSum (M := M) (S := S) (hc := hc)
  let B := measuredGammaDirectSumToPresentation (M := M) (S := S) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (measuredGammaSemiringPresentation hc S)
    rintro ⟨k, U⟩
    change B (F (measuredGammaSemiringClass U)) = measuredGammaSemiringClass U
    rw [measuredGammaPresentationToDirectSum_class, measuredGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := measuredGammaClass_surjective a
      change F (B (measuredGammaDirectSumClass hc U)) = measuredGammaDirectSumClass hc U
      rw [measuredGammaDirectSumToPresentation_class, measuredGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
