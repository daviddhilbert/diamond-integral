import «section 3».GammaGroundMeasuredGammaGradedSemiring
import «section 3».GammaGroundMeasuredGammaSemiring
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

def gammaGroundMeasuredGammaDirectSumInvariant : PositiveGrothendieck.Invariant (gammaGroundMeasuredGammaSemiringPresentation hc (M := M) ground)
    (R := GammaGroundMeasuredGammaDirectSum (M := M) hc ground) where
  toFun A := gammaGroundMeasuredGammaDirectSumClass hc A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k) (gammaGroundMeasuredGammaClass_iso e)
  empty := by
    change DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) 0 (gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.empty hc ground 0)) = 0
    rw [gammaGroundMeasuredGammaClass_empty, map_zero]
  unit := rfl
  product A B := gammaGroundMeasuredGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass a) + DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass b) =
        DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass d) + DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k (gammaGroundMeasuredGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k) (positiveClass_scissor (gammaGroundMeasuredGammaPresentation hc ground k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaGroundMeasuredGammaDirectSumClass, gammaGroundMeasuredGammaClass_empty, map_zero, add_zero]

def gammaGroundMeasuredGammaPresentationToDirectSum : GammaGroundMeasuredGammaPositiveSemiring (M := M) hc ground →+* GammaGroundMeasuredGammaDirectSum hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredGammaSemiringPresentation hc ground) gammaGroundMeasuredGammaDirectSumInvariant

@[simp] theorem gammaGroundMeasuredGammaPresentationToDirectSum_class {k : ℕ} (U : GammaGroundMeasuredGammaObject (M := M) hc ground k) :
    gammaGroundMeasuredGammaPresentationToDirectSum (gammaGroundMeasuredGammaSemiringClass U) = gammaGroundMeasuredGammaDirectSumClass hc U :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredGammaSemiringPresentation hc ground)
    (gammaGroundMeasuredGammaDirectSumInvariant (M := M) (ground := ground)) ⟨k, U⟩

def gammaGroundMeasuredGammaDirectSumToPresentationAdd : GammaGroundMeasuredGammaDirectSum (M := M) hc ground →+ GammaGroundMeasuredGammaPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundMeasuredGammaKPlusToSemiring)

@[simp] theorem gammaGroundMeasuredGammaDirectSumToPresentationAdd_of (k : ℕ) (a : GammaGroundMeasuredGammaKPlus (M := M) hc ground k) :
    gammaGroundMeasuredGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) k a) = gammaGroundMeasuredGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundMeasuredGammaDirectSumToPresentationAdd_one :
    gammaGroundMeasuredGammaDirectSumToPresentationAdd (1 : GammaGroundMeasuredGammaDirectSum (M := M) hc ground) = 1 := by
  change gammaGroundMeasuredGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) 0 (gammaGroundMeasuredGammaClass (GammaGroundMeasuredGammaObject.unit hc ground))) = 1
  rw [gammaGroundMeasuredGammaDirectSumToPresentationAdd_of, gammaGroundMeasuredGammaKPlusToSemiring_class, gammaGroundMeasuredGammaSemiringClass_unit]

theorem gammaGroundMeasuredGammaDirectSumToPresentationAdd_mul (a b : GammaGroundMeasuredGammaDirectSum (M := M) hc ground) :
    gammaGroundMeasuredGammaDirectSumToPresentationAdd (a * b) =
      gammaGroundMeasuredGammaDirectSumToPresentationAdd a * gammaGroundMeasuredGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
      obtain ⟨V, rfl⟩ := gammaGroundMeasuredGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaGroundMeasuredGammaDirectSumToPresentationAdd
        (DirectSum.of (GammaGroundMeasuredGammaKPlus hc ground) (i + j) (gammaGroundMeasuredGammaClassMul (gammaGroundMeasuredGammaClass U) (gammaGroundMeasuredGammaClass V))) = _
      rw [gammaGroundMeasuredGammaClassMul_class, gammaGroundMeasuredGammaDirectSumToPresentationAdd_of,
        gammaGroundMeasuredGammaDirectSumToPresentationAdd_of, gammaGroundMeasuredGammaDirectSumToPresentationAdd_of,
        gammaGroundMeasuredGammaKPlusToSemiring_class, gammaGroundMeasuredGammaKPlusToSemiring_class, gammaGroundMeasuredGammaKPlusToSemiring_class,
        gammaGroundMeasuredGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaGroundMeasuredGammaDirectSumToPresentation : GammaGroundMeasuredGammaDirectSum (M := M) hc ground →+* GammaGroundMeasuredGammaPositiveSemiring hc ground where
  __ := gammaGroundMeasuredGammaDirectSumToPresentationAdd
  map_one' := gammaGroundMeasuredGammaDirectSumToPresentationAdd_one
  map_mul' := gammaGroundMeasuredGammaDirectSumToPresentationAdd_mul

@[simp] theorem gammaGroundMeasuredGammaDirectSumToPresentation_class {k : ℕ} (U : GammaGroundMeasuredGammaObject (M := M) hc ground k) :
    gammaGroundMeasuredGammaDirectSumToPresentation (gammaGroundMeasuredGammaDirectSumClass hc U) = gammaGroundMeasuredGammaSemiringClass U :=
  (gammaGroundMeasuredGammaDirectSumToPresentationAdd_of k (gammaGroundMeasuredGammaClass U)).trans (gammaGroundMeasuredGammaKPlusToSemiring_class U)

def gammaGroundMeasuredGammaSemiringEquivDirectSum : GammaGroundMeasuredGammaPositiveSemiring (M := M) hc ground ≃+* GammaGroundMeasuredGammaDirectSum hc ground := by
  let F := gammaGroundMeasuredGammaPresentationToDirectSum (M := M) (ground := ground) (hc := hc)
  let B := gammaGroundMeasuredGammaDirectSumToPresentation (M := M) (ground := ground) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundMeasuredGammaSemiringPresentation hc ground)
    rintro ⟨k, U⟩
    change B (F (gammaGroundMeasuredGammaSemiringClass U)) = gammaGroundMeasuredGammaSemiringClass U
    rw [gammaGroundMeasuredGammaPresentationToDirectSum_class, gammaGroundMeasuredGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaGroundMeasuredGammaClass_surjective a
      change F (B (gammaGroundMeasuredGammaDirectSumClass hc U)) = gammaGroundMeasuredGammaDirectSumClass hc U
      rw [gammaGroundMeasuredGammaDirectSumToPresentation_class, gammaGroundMeasuredGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
