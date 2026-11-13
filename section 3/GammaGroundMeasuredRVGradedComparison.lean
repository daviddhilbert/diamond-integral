import «section 3».GammaGroundMeasuredRVGradedSemiring

/-! The universal semiring presentation is exactly the direct sum of
the genuine fixed-degree positive scissors. In particular, supplying
multiplication has introduced no unintended additive identifications. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundMeasuredRVDirectSumInvariant : PositiveGrothendieck.Invariant (gammaGroundMeasuredRVSemiringPresentation hc ground)
    (R := GammaGroundMeasuredRVDirectSum hc ground) where
  toFun A := gammaGroundMeasuredRVDirectSumClass A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k) (gammaGroundMeasuredRVClass_iso e)
  empty := by
    change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.empty hc ground 0)) = 0
    rw [gammaGroundMeasuredRVClass_empty, map_zero]
  unit := rfl
  product A B := gammaGroundMeasuredRVDirectSumClass_product A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass a) + DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass b) =
        DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass d) + DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k (gammaGroundMeasuredRVClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k) (positiveClass_scissor (gammaGroundMeasuredRVPresentation hc ground k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaGroundMeasuredRVDirectSumClass, gammaGroundMeasuredRVClass_empty, map_zero, add_zero]

def gammaGroundMeasuredRVPresentationToDirectSum : GammaGroundMeasuredRVPositiveSemiring hc ground →+* GammaGroundMeasuredRVDirectSum hc ground :=
  PositiveGrothendieck.lift (gammaGroundMeasuredRVSemiringPresentation hc ground) gammaGroundMeasuredRVDirectSumInvariant

@[simp] theorem gammaGroundMeasuredRVPresentationToDirectSum_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVSemiringClass U) = gammaGroundMeasuredRVDirectSumClass U :=
  PositiveGrothendieck.lift_of (gammaGroundMeasuredRVSemiringPresentation hc ground)
    (gammaGroundMeasuredRVDirectSumInvariant (M := M) (hc := hc) (ground := ground)) ⟨k, U⟩

def gammaGroundMeasuredRVDirectSumToPresentationAdd : GammaGroundMeasuredRVDirectSum hc ground →+ GammaGroundMeasuredRVPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundMeasuredRVKPlusToSemiring)

@[simp] theorem gammaGroundMeasuredRVDirectSumToPresentationAdd_of (k : ℕ) (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVDirectSumToPresentationAdd (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) k a) = gammaGroundMeasuredRVKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundMeasuredRVDirectSumToPresentationAdd_one :
    gammaGroundMeasuredRVDirectSumToPresentationAdd (1 : GammaGroundMeasuredRVDirectSum hc ground) = 1 := by
  change gammaGroundMeasuredRVDirectSumToPresentationAdd (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) 0 (gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.unit hc ground))) = 1
  rw [gammaGroundMeasuredRVDirectSumToPresentationAdd_of, gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVSemiringClass_unit]

theorem gammaGroundMeasuredRVDirectSumToPresentationAdd_mul (a b : GammaGroundMeasuredRVDirectSum hc ground) :
    gammaGroundMeasuredRVDirectSumToPresentationAdd (a * b) =
      gammaGroundMeasuredRVDirectSumToPresentationAdd a * gammaGroundMeasuredRVDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
      obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaGroundMeasuredRVDirectSumToPresentationAdd
        (DirectSum.of (GammaGroundMeasuredRVKPlus hc ground) (i + j) (gammaGroundMeasuredRVClassMul (gammaGroundMeasuredRVClass U) (gammaGroundMeasuredRVClass V))) = _
      rw [gammaGroundMeasuredRVClassMul_class, gammaGroundMeasuredRVDirectSumToPresentationAdd_of,
        gammaGroundMeasuredRVDirectSumToPresentationAdd_of, gammaGroundMeasuredRVDirectSumToPresentationAdd_of,
        gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVKPlusToSemiring_class, gammaGroundMeasuredRVKPlusToSemiring_class,
        gammaGroundMeasuredRVSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaGroundMeasuredRVDirectSumToPresentation : GammaGroundMeasuredRVDirectSum hc ground →+* GammaGroundMeasuredRVPositiveSemiring hc ground where
  __ := gammaGroundMeasuredRVDirectSumToPresentationAdd
  map_one' := gammaGroundMeasuredRVDirectSumToPresentationAdd_one
  map_mul' := gammaGroundMeasuredRVDirectSumToPresentationAdd_mul

@[simp] theorem gammaGroundMeasuredRVDirectSumToPresentation_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVDirectSumToPresentation (gammaGroundMeasuredRVDirectSumClass U) = gammaGroundMeasuredRVSemiringClass U :=
  (gammaGroundMeasuredRVDirectSumToPresentationAdd_of k (gammaGroundMeasuredRVClass U)).trans (gammaGroundMeasuredRVKPlusToSemiring_class U)

def gammaGroundMeasuredRVSemiringEquivDirectSum : GammaGroundMeasuredRVPositiveSemiring hc ground ≃+* GammaGroundMeasuredRVDirectSum hc ground := by
  let F := gammaGroundMeasuredRVPresentationToDirectSum (M := M) (hc := hc) (ground := ground)
  let B := gammaGroundMeasuredRVDirectSumToPresentation (M := M) (hc := hc) (ground := ground)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundMeasuredRVSemiringPresentation hc ground)
    rintro ⟨k, U⟩
    change B (F (gammaGroundMeasuredRVSemiringClass U)) = gammaGroundMeasuredRVSemiringClass U
    rw [gammaGroundMeasuredRVPresentationToDirectSum_class, gammaGroundMeasuredRVDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
      change F (B (gammaGroundMeasuredRVDirectSumClass U)) = gammaGroundMeasuredRVDirectSumClass U
      rw [gammaGroundMeasuredRVDirectSumToPresentation_class, gammaGroundMeasuredRVPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
