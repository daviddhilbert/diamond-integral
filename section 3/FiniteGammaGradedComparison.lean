import «section 3».FiniteGammaGradedSemiring
import «section 3».FiniteGammaSemiring

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

def finiteGammaDirectSumInvariant : PositiveGrothendieck.Invariant (finiteGammaSemiringPresentation hc (M := M) S)
    (R := FiniteGammaDirectSum (M := M) hc S) where
  toFun A := finiteGammaDirectSumClass A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (FiniteGammaKPlus hc S) k) (finiteGammaClass_iso e)
  empty := by
    change DirectSum.of (FiniteGammaKPlus hc S) 0 (finiteGammaClass (FiniteGammaObject.empty hc S 0)) = 0
    rw [finiteGammaClass_empty, map_zero]
  unit := rfl
  product A B := finiteGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (FiniteGammaKPlus hc S) k (finiteGammaClass a) + DirectSum.of (FiniteGammaKPlus hc S) k (finiteGammaClass b) =
        DirectSum.of (FiniteGammaKPlus hc S) k (finiteGammaClass d) + DirectSum.of (FiniteGammaKPlus hc S) k (finiteGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (FiniteGammaKPlus hc S) k) (positiveClass_scissor (finiteGammaPresentation hc S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [finiteGammaDirectSumClass, finiteGammaClass_empty, map_zero, add_zero]

def finiteGammaPresentationToDirectSum : FiniteGammaPositiveSemiring (M := M) hc S →+* FiniteGammaDirectSum hc S :=
  PositiveGrothendieck.lift (finiteGammaSemiringPresentation hc S) finiteGammaDirectSumInvariant

@[simp] theorem finiteGammaPresentationToDirectSum_class {k : ℕ} (U : FiniteGammaObject (M := M) hc S k) :
    finiteGammaPresentationToDirectSum (finiteGammaSemiringClass U) = finiteGammaDirectSumClass U :=
  PositiveGrothendieck.lift_of (finiteGammaSemiringPresentation hc S)
    (finiteGammaDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def finiteGammaDirectSumToPresentationAdd : FiniteGammaDirectSum (M := M) hc S →+ FiniteGammaPositiveSemiring hc S :=
  DirectSum.toAddMonoid (fun _ => finiteGammaKPlusToSemiring)

@[simp] theorem finiteGammaDirectSumToPresentationAdd_of (k : ℕ) (a : FiniteGammaKPlus (M := M) hc S k) :
    finiteGammaDirectSumToPresentationAdd (DirectSum.of (FiniteGammaKPlus hc S) k a) = finiteGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem finiteGammaDirectSumToPresentationAdd_one :
    finiteGammaDirectSumToPresentationAdd (1 : FiniteGammaDirectSum (M := M) hc S) = 1 := by
  change finiteGammaDirectSumToPresentationAdd (DirectSum.of (FiniteGammaKPlus hc S) 0 (finiteGammaClass (FiniteGammaObject.unit hc S))) = 1
  rw [finiteGammaDirectSumToPresentationAdd_of, finiteGammaKPlusToSemiring_class, finiteGammaSemiringClass_unit]

theorem finiteGammaDirectSumToPresentationAdd_mul (a b : FiniteGammaDirectSum (M := M) hc S) :
    finiteGammaDirectSumToPresentationAdd (a * b) =
      finiteGammaDirectSumToPresentationAdd a * finiteGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := finiteGammaClass_surjective a
      obtain ⟨V, rfl⟩ := finiteGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change finiteGammaDirectSumToPresentationAdd
        (DirectSum.of (FiniteGammaKPlus hc S) (i + j) (finiteGammaClassMul (finiteGammaClass U) (finiteGammaClass V))) = _
      rw [finiteGammaClassMul_class, finiteGammaDirectSumToPresentationAdd_of,
        finiteGammaDirectSumToPresentationAdd_of, finiteGammaDirectSumToPresentationAdd_of,
        finiteGammaKPlusToSemiring_class, finiteGammaKPlusToSemiring_class, finiteGammaKPlusToSemiring_class,
        finiteGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def finiteGammaDirectSumToPresentation : FiniteGammaDirectSum (M := M) hc S →+* FiniteGammaPositiveSemiring hc S where
  __ := finiteGammaDirectSumToPresentationAdd
  map_one' := finiteGammaDirectSumToPresentationAdd_one
  map_mul' := finiteGammaDirectSumToPresentationAdd_mul

@[simp] theorem finiteGammaDirectSumToPresentation_class {k : ℕ} (U : FiniteGammaObject (M := M) hc S k) :
    finiteGammaDirectSumToPresentation (finiteGammaDirectSumClass U) = finiteGammaSemiringClass U :=
  (finiteGammaDirectSumToPresentationAdd_of k (finiteGammaClass U)).trans (finiteGammaKPlusToSemiring_class U)

def finiteGammaSemiringEquivDirectSum : FiniteGammaPositiveSemiring (M := M) hc S ≃+* FiniteGammaDirectSum hc S := by
  let F := finiteGammaPresentationToDirectSum (M := M) (S := S) (hc := hc)
  let B := finiteGammaDirectSumToPresentation (M := M) (S := S) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (finiteGammaSemiringPresentation hc S)
    rintro ⟨k, U⟩
    change B (F (finiteGammaSemiringClass U)) = finiteGammaSemiringClass U
    rw [finiteGammaPresentationToDirectSum_class, finiteGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := finiteGammaClass_surjective a
      change F (B (finiteGammaDirectSumClass U)) = finiteGammaDirectSumClass U
      rw [finiteGammaDirectSumToPresentation_class, finiteGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
