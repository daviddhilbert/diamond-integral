import «section 3».GammaGroundGammaGradedSemiring
import «section 3».GammaGroundGammaSemiring
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

def gammaGroundGammaDirectSumInvariant : PositiveGrothendieck.Invariant (gammaGroundGammaSemiringPresentation hc (M := M) ground)
    (R := GammaGroundGammaDirectSum (M := M) hc ground) where
  toFun A := gammaGroundGammaDirectSumClass hc A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (GammaGroundGammaKPlus hc ground) k) (gammaGroundGammaClass_iso e)
  empty := by
    change DirectSum.of (GammaGroundGammaKPlus hc ground) 0 (gammaGroundGammaClass (GammaGroundGammaObject.empty hc ground 0)) = 0
    rw [gammaGroundGammaClass_empty, map_zero]
  unit := rfl
  product A B := gammaGroundGammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass a) + DirectSum.of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass b) =
        DirectSum.of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass d) + DirectSum.of (GammaGroundGammaKPlus hc ground) k (gammaGroundGammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaGroundGammaKPlus hc ground) k) (positiveClass_scissor (gammaGroundGammaPresentation hc ground k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaGroundGammaDirectSumClass, gammaGroundGammaClass_empty, map_zero, add_zero]

def gammaGroundGammaPresentationToDirectSum : GammaGroundGammaPositiveSemiring (M := M) hc ground →+* GammaGroundGammaDirectSum hc ground :=
  PositiveGrothendieck.lift (gammaGroundGammaSemiringPresentation hc ground) gammaGroundGammaDirectSumInvariant

@[simp] theorem gammaGroundGammaPresentationToDirectSum_class {k : ℕ} (U : GammaGroundGammaObject (M := M) hc ground k) :
    gammaGroundGammaPresentationToDirectSum (gammaGroundGammaSemiringClass U) = gammaGroundGammaDirectSumClass hc U :=
  PositiveGrothendieck.lift_of (gammaGroundGammaSemiringPresentation hc ground)
    (gammaGroundGammaDirectSumInvariant (M := M) (ground := ground)) ⟨k, U⟩

def gammaGroundGammaDirectSumToPresentationAdd : GammaGroundGammaDirectSum (M := M) hc ground →+ GammaGroundGammaPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundGammaKPlusToSemiring)

@[simp] theorem gammaGroundGammaDirectSumToPresentationAdd_of (k : ℕ) (a : GammaGroundGammaKPlus (M := M) hc ground k) :
    gammaGroundGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundGammaKPlus hc ground) k a) = gammaGroundGammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundGammaDirectSumToPresentationAdd_one :
    gammaGroundGammaDirectSumToPresentationAdd (1 : GammaGroundGammaDirectSum (M := M) hc ground) = 1 := by
  change gammaGroundGammaDirectSumToPresentationAdd (DirectSum.of (GammaGroundGammaKPlus hc ground) 0 (gammaGroundGammaClass (GammaGroundGammaObject.unit hc ground))) = 1
  rw [gammaGroundGammaDirectSumToPresentationAdd_of, gammaGroundGammaKPlusToSemiring_class, gammaGroundGammaSemiringClass_unit]

theorem gammaGroundGammaDirectSumToPresentationAdd_mul (a b : GammaGroundGammaDirectSum (M := M) hc ground) :
    gammaGroundGammaDirectSumToPresentationAdd (a * b) =
      gammaGroundGammaDirectSumToPresentationAdd a * gammaGroundGammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
      obtain ⟨V, rfl⟩ := gammaGroundGammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaGroundGammaDirectSumToPresentationAdd
        (DirectSum.of (GammaGroundGammaKPlus hc ground) (i + j) (gammaGroundGammaClassMul (gammaGroundGammaClass U) (gammaGroundGammaClass V))) = _
      rw [gammaGroundGammaClassMul_class, gammaGroundGammaDirectSumToPresentationAdd_of,
        gammaGroundGammaDirectSumToPresentationAdd_of, gammaGroundGammaDirectSumToPresentationAdd_of,
        gammaGroundGammaKPlusToSemiring_class, gammaGroundGammaKPlusToSemiring_class, gammaGroundGammaKPlusToSemiring_class,
        gammaGroundGammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaGroundGammaDirectSumToPresentation : GammaGroundGammaDirectSum (M := M) hc ground →+* GammaGroundGammaPositiveSemiring hc ground where
  __ := gammaGroundGammaDirectSumToPresentationAdd
  map_one' := gammaGroundGammaDirectSumToPresentationAdd_one
  map_mul' := gammaGroundGammaDirectSumToPresentationAdd_mul

@[simp] theorem gammaGroundGammaDirectSumToPresentation_class {k : ℕ} (U : GammaGroundGammaObject (M := M) hc ground k) :
    gammaGroundGammaDirectSumToPresentation (gammaGroundGammaDirectSumClass hc U) = gammaGroundGammaSemiringClass U :=
  (gammaGroundGammaDirectSumToPresentationAdd_of k (gammaGroundGammaClass U)).trans (gammaGroundGammaKPlusToSemiring_class U)

def gammaGroundGammaSemiringEquivDirectSum : GammaGroundGammaPositiveSemiring (M := M) hc ground ≃+* GammaGroundGammaDirectSum hc ground := by
  let F := gammaGroundGammaPresentationToDirectSum (M := M) (ground := ground) (hc := hc)
  let B := gammaGroundGammaDirectSumToPresentation (M := M) (ground := ground) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundGammaSemiringPresentation hc ground)
    rintro ⟨k, U⟩
    change B (F (gammaGroundGammaSemiringClass U)) = gammaGroundGammaSemiringClass U
    rw [gammaGroundGammaPresentationToDirectSum_class, gammaGroundGammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaGroundGammaClass_surjective a
      change F (B (gammaGroundGammaDirectSumClass hc U)) = gammaGroundGammaDirectSumClass hc U
      rw [gammaGroundGammaDirectSumToPresentation_class, gammaGroundGammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
