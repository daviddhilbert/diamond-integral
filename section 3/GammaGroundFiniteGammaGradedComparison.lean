import «section 3».GammaGroundFiniteGammaGradedSemiring
import «section 3».GammaGroundFiniteGammaSemiring
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

def gammaGroundFiniteGammaDirectSumInvariant : PositiveGrothendieck.Invariant (gammaGroundFiniteGammaSemiringPresentation hc (M := M) ground)
    (R := GammaGroundFiniteGammaDirectSum (M := M) hc ground) where
  toFun A := gammaGroundFiniteGammaDirectSumClass A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k) (gammaGroundFiniteGammaClass_iso e)
  empty := by
    change DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) 0 (gammaGroundFiniteGammaClass (GammaGroundFiniteGammaObject.empty hc ground 0)) = 0
    rw [gammaGroundFiniteGammaClass_empty, map_zero]
  unit := rfl
  product A B := gammaGroundFiniteGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass a) + DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass b) =
        DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass d) + DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k (gammaGroundFiniteGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k) (positiveClass_scissor (gammaGroundFiniteGammaPresentation hc ground k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaGroundFiniteGammaDirectSumClass, gammaGroundFiniteGammaClass_empty, map_zero, add_zero]

def gammaGroundFiniteGammaPresentationToDirectSum : GammaGroundFiniteGammaPositiveSemiring (M := M) hc ground →+* GammaGroundFiniteGammaDirectSum hc ground :=
  PositiveGrothendieck.lift (gammaGroundFiniteGammaSemiringPresentation hc ground) gammaGroundFiniteGammaDirectSumInvariant

@[simp] theorem gammaGroundFiniteGammaPresentationToDirectSum_class {k : ℕ} (U : GammaGroundFiniteGammaObject (M := M) hc ground k) :
    gammaGroundFiniteGammaPresentationToDirectSum (gammaGroundFiniteGammaSemiringClass U) = gammaGroundFiniteGammaDirectSumClass U :=
  PositiveGrothendieck.lift_of (gammaGroundFiniteGammaSemiringPresentation hc ground)
    (gammaGroundFiniteGammaDirectSumInvariant (M := M) (ground := ground)) ⟨k, U⟩

def gammaGroundFiniteGammaDirectSumToPresentationAdd : GammaGroundFiniteGammaDirectSum (M := M) hc ground →+ GammaGroundFiniteGammaPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundFiniteGammaKPlusToSemiring)

@[simp] theorem gammaGroundFiniteGammaDirectSumToPresentationAdd_of (k : ℕ) (a : GammaGroundFiniteGammaKPlus (M := M) hc ground k) :
    gammaGroundFiniteGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) k a) = gammaGroundFiniteGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundFiniteGammaDirectSumToPresentationAdd_one :
    gammaGroundFiniteGammaDirectSumToPresentationAdd (1 : GammaGroundFiniteGammaDirectSum (M := M) hc ground) = 1 := by
  change gammaGroundFiniteGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) 0 (gammaGroundFiniteGammaClass (GammaGroundFiniteGammaObject.unit hc ground))) = 1
  rw [gammaGroundFiniteGammaDirectSumToPresentationAdd_of, gammaGroundFiniteGammaKPlusToSemiring_class, gammaGroundFiniteGammaSemiringClass_unit]

theorem gammaGroundFiniteGammaDirectSumToPresentationAdd_mul (a b : GammaGroundFiniteGammaDirectSum (M := M) hc ground) :
    gammaGroundFiniteGammaDirectSumToPresentationAdd (a * b) =
      gammaGroundFiniteGammaDirectSumToPresentationAdd a * gammaGroundFiniteGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaGroundFiniteGammaClass_surjective a
      obtain ⟨V, rfl⟩ := gammaGroundFiniteGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaGroundFiniteGammaDirectSumToPresentationAdd
        (DirectSum.of (GammaGroundFiniteGammaKPlus hc ground) (i + j) (gammaGroundFiniteGammaClassMul (gammaGroundFiniteGammaClass U) (gammaGroundFiniteGammaClass V))) = _
      rw [gammaGroundFiniteGammaClassMul_class, gammaGroundFiniteGammaDirectSumToPresentationAdd_of,
        gammaGroundFiniteGammaDirectSumToPresentationAdd_of, gammaGroundFiniteGammaDirectSumToPresentationAdd_of,
        gammaGroundFiniteGammaKPlusToSemiring_class, gammaGroundFiniteGammaKPlusToSemiring_class, gammaGroundFiniteGammaKPlusToSemiring_class,
        gammaGroundFiniteGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaGroundFiniteGammaDirectSumToPresentation : GammaGroundFiniteGammaDirectSum (M := M) hc ground →+* GammaGroundFiniteGammaPositiveSemiring hc ground where
  __ := gammaGroundFiniteGammaDirectSumToPresentationAdd
  map_one' := gammaGroundFiniteGammaDirectSumToPresentationAdd_one
  map_mul' := gammaGroundFiniteGammaDirectSumToPresentationAdd_mul

@[simp] theorem gammaGroundFiniteGammaDirectSumToPresentation_class {k : ℕ} (U : GammaGroundFiniteGammaObject (M := M) hc ground k) :
    gammaGroundFiniteGammaDirectSumToPresentation (gammaGroundFiniteGammaDirectSumClass U) = gammaGroundFiniteGammaSemiringClass U :=
  (gammaGroundFiniteGammaDirectSumToPresentationAdd_of k (gammaGroundFiniteGammaClass U)).trans (gammaGroundFiniteGammaKPlusToSemiring_class U)

def gammaGroundFiniteGammaSemiringEquivDirectSum : GammaGroundFiniteGammaPositiveSemiring (M := M) hc ground ≃+* GammaGroundFiniteGammaDirectSum hc ground := by
  let F := gammaGroundFiniteGammaPresentationToDirectSum (M := M) (ground := ground) (hc := hc)
  let B := gammaGroundFiniteGammaDirectSumToPresentation (M := M) (ground := ground) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundFiniteGammaSemiringPresentation hc ground)
    rintro ⟨k, U⟩
    change B (F (gammaGroundFiniteGammaSemiringClass U)) = gammaGroundFiniteGammaSemiringClass U
    rw [gammaGroundFiniteGammaPresentationToDirectSum_class, gammaGroundFiniteGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaGroundFiniteGammaClass_surjective a
      change F (B (gammaGroundFiniteGammaDirectSumClass U)) = gammaGroundFiniteGammaDirectSumClass U
      rw [gammaGroundFiniteGammaDirectSumToPresentation_class, gammaGroundFiniteGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
