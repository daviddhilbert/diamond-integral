import «section 3».GammaGroundMeasuredFiniteGammaGradedSemiring
import «section 3».GammaGroundMeasuredFiniteGammaSemiring
/-! The universal semiring presentation is exactly the direct sum of
the genuine fixed-degree positive scissors. In particular, supplying
multiplication has introduced no unintended additive identifications. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {ground : GammaParameters.Base (M := M)}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def gammaGroundMeasuredFiniteGammaDirectSumInvariant : PositiveGrothendieck.Invariant (gammaGroundMeasuredFiniteGammaSemiringPresentation hc (M := M) ground)
    (R := GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) where
  toFun A := gammaGroundMeasuredFiniteGammaDirectSumClass A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k) (gammaGroundMeasuredFiniteGammaClass_iso e)
  empty := by
    change DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) 0 (gammaGroundMeasuredFiniteGammaClass (GammaGroundMeasuredFiniteGammaObject.empty hc ground 0)) = 0
    rw [gammaGroundMeasuredFiniteGammaClass_empty, map_zero]
  unit := rfl
  product A B := gammaGroundMeasuredFiniteGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass a) + DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass b) =
        DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass d) + DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k (gammaGroundMeasuredFiniteGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k) (positiveClass_scissor (gammaGroundMeasuredFiniteGammaPresentation hc ground k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaGroundMeasuredFiniteGammaDirectSumClass, gammaGroundMeasuredFiniteGammaClass_empty, map_zero, add_zero]

def gammaGroundMeasuredFiniteGammaPresentationToDirectSum : GammaGroundMeasuredFiniteGammaPositiveSemiring (M := M) hc ground →+* GammaGroundMeasuredFiniteGammaDirectSum hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) gammaGroundMeasuredFiniteGammaDirectSumInvariant

@[simp] theorem gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class {k : ℕ} (U : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground k) :
    gammaGroundMeasuredFiniteGammaPresentationToDirectSum (gammaGroundMeasuredFiniteGammaSemiringClass U) = gammaGroundMeasuredFiniteGammaDirectSumClass U :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground)
    (gammaGroundMeasuredFiniteGammaDirectSumInvariant (M := M) (ground := ground)) ⟨k, U⟩

def gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground →+ GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundMeasuredFiniteGammaKPlusToSemiring)

@[simp] theorem gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_of (k : ℕ) (a : GammaGroundMeasuredFiniteGammaKPlus (M := M) hc ground k) :
    gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) k a) = gammaGroundMeasuredFiniteGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_one :
    gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd (1 : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) = 1 := by
  change gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) 0 (gammaGroundMeasuredFiniteGammaClass (GammaGroundMeasuredFiniteGammaObject.unit hc ground))) = 1
  rw [gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_of, gammaGroundMeasuredFiniteGammaKPlusToSemiring_class, gammaGroundMeasuredFiniteGammaSemiringClass_unit]

theorem gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_mul (a b : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground) :
    gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd (a * b) =
      gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd a * gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaGroundMeasuredFiniteGammaClass_surjective a
      obtain ⟨V, rfl⟩ := gammaGroundMeasuredFiniteGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd
        (DirectSum.of (GammaGroundMeasuredFiniteGammaKPlus hc ground) (i + j) (gammaGroundMeasuredFiniteGammaClassMul (gammaGroundMeasuredFiniteGammaClass U) (gammaGroundMeasuredFiniteGammaClass V))) = _
      rw [gammaGroundMeasuredFiniteGammaClassMul_class, gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_of,
        gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_of, gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_of,
        gammaGroundMeasuredFiniteGammaKPlusToSemiring_class, gammaGroundMeasuredFiniteGammaKPlusToSemiring_class, gammaGroundMeasuredFiniteGammaKPlusToSemiring_class,
        gammaGroundMeasuredFiniteGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaGroundMeasuredFiniteGammaDirectSumToPresentation : GammaGroundMeasuredFiniteGammaDirectSum (M := M) hc ground →+* GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground where
  __ := gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd
  map_one' := gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_one
  map_mul' := gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_mul

@[simp] theorem gammaGroundMeasuredFiniteGammaDirectSumToPresentation_class {k : ℕ} (U : GammaGroundMeasuredFiniteGammaObject (M := M) hc ground k) :
    gammaGroundMeasuredFiniteGammaDirectSumToPresentation (gammaGroundMeasuredFiniteGammaDirectSumClass U) = gammaGroundMeasuredFiniteGammaSemiringClass U :=
  (gammaGroundMeasuredFiniteGammaDirectSumToPresentationAdd_of k (gammaGroundMeasuredFiniteGammaClass U)).trans (gammaGroundMeasuredFiniteGammaKPlusToSemiring_class U)

def gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum : GammaGroundMeasuredFiniteGammaPositiveSemiring (M := M) hc ground ≃+* GammaGroundMeasuredFiniteGammaDirectSum hc ground := by
  let F := gammaGroundMeasuredFiniteGammaPresentationToDirectSum (M := M) (ground := ground) (hc := hc)
  let B := gammaGroundMeasuredFiniteGammaDirectSumToPresentation (M := M) (ground := ground) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground)
    rintro ⟨k, U⟩
    change B (F (gammaGroundMeasuredFiniteGammaSemiringClass U)) = gammaGroundMeasuredFiniteGammaSemiringClass U
    rw [gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class, gammaGroundMeasuredFiniteGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaGroundMeasuredFiniteGammaClass_surjective a
      change F (B (gammaGroundMeasuredFiniteGammaDirectSumClass U)) = gammaGroundMeasuredFiniteGammaDirectSumClass U
      rw [gammaGroundMeasuredFiniteGammaDirectSumToPresentation_class, gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
