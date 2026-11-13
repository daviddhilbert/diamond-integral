import «section 3».GammaGroundRVGradedSemiring

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

def gammaGroundRVDirectSumInvariant : PositiveGrothendieck.Invariant (gammaGroundRVSemiringPresentation hc ground)
    (R := GammaGroundRVDirectSum hc ground) where
  toFun A := gammaGroundRVDirectSumClass A.2
  iso := by
    rintro ⟨k, A⟩ ⟨l, B⟩ ⟨he, ⟨f⟩⟩
    change k = l at he
    subst l
    exact congrArg (DirectSum.of (GammaGroundRVKPlus hc ground) k) (gammaGroundRVClass_iso (asIso (show A ⟶ B from f)))
  empty := by
    change DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundRVObject.empty hc ground 0)) = 0
    rw [gammaGroundRVClass_empty, map_zero]
  unit := rfl
  product A B := gammaGroundRVDirectSumClass_product A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass a) + DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass b) =
        DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass d) + DirectSum.of (GammaGroundRVKPlus hc ground) k (gammaGroundRVClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaGroundRVKPlus hc ground) k) (positiveClass_scissor (gammaGroundRVPresentation hc ground k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaGroundRVDirectSumClass, gammaGroundRVClass_empty, map_zero, add_zero]

def gammaGroundRVPresentationToDirectSum : GammaGroundRVPositiveSemiring hc ground →+* GammaGroundRVDirectSum hc ground :=
  PositiveGrothendieck.lift (gammaGroundRVSemiringPresentation hc ground) gammaGroundRVDirectSumInvariant

@[simp] theorem gammaGroundRVPresentationToDirectSum_class {k : ℕ} (U : GammaGroundRVObject hc ground k) :
    gammaGroundRVPresentationToDirectSum (gammaGroundRVSemiringClass U) = gammaGroundRVDirectSumClass U :=
  PositiveGrothendieck.lift_of (gammaGroundRVSemiringPresentation hc ground)
    (gammaGroundRVDirectSumInvariant (M := M) (hc := hc) (ground := ground)) ⟨k, U⟩

def gammaGroundRVDirectSumToPresentationAdd : GammaGroundRVDirectSum hc ground →+ GammaGroundRVPositiveSemiring hc ground :=
  DirectSum.toAddMonoid (fun _ => gammaGroundRVKPlusToSemiring)

@[simp] theorem gammaGroundRVDirectSumToPresentationAdd_of (k : ℕ) (a : GammaGroundRVKPlus hc ground k) :
    gammaGroundRVDirectSumToPresentationAdd (DirectSum.of (GammaGroundRVKPlus hc ground) k a) = gammaGroundRVKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaGroundRVDirectSumToPresentationAdd_one :
    gammaGroundRVDirectSumToPresentationAdd (1 : GammaGroundRVDirectSum hc ground) = 1 := by
  change gammaGroundRVDirectSumToPresentationAdd (DirectSum.of (GammaGroundRVKPlus hc ground) 0 (gammaGroundRVClass (GammaGroundRVObject.unit hc ground))) = 1
  rw [gammaGroundRVDirectSumToPresentationAdd_of, gammaGroundRVKPlusToSemiring_class, gammaGroundRVSemiringClass_unit]

theorem gammaGroundRVDirectSumToPresentationAdd_mul (a b : GammaGroundRVDirectSum hc ground) :
    gammaGroundRVDirectSumToPresentationAdd (a * b) =
      gammaGroundRVDirectSumToPresentationAdd a * gammaGroundRVDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
      obtain ⟨V, rfl⟩ := gammaGroundRVClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaGroundRVDirectSumToPresentationAdd
        (DirectSum.of (GammaGroundRVKPlus hc ground) (i + j) (gammaGroundRVClassMul (gammaGroundRVClass U) (gammaGroundRVClass V))) = _
      rw [gammaGroundRVClassMul_class, gammaGroundRVDirectSumToPresentationAdd_of,
        gammaGroundRVDirectSumToPresentationAdd_of, gammaGroundRVDirectSumToPresentationAdd_of,
        gammaGroundRVKPlusToSemiring_class, gammaGroundRVKPlusToSemiring_class, gammaGroundRVKPlusToSemiring_class,
        gammaGroundRVSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaGroundRVDirectSumToPresentation : GammaGroundRVDirectSum hc ground →+* GammaGroundRVPositiveSemiring hc ground where
  __ := gammaGroundRVDirectSumToPresentationAdd
  map_one' := gammaGroundRVDirectSumToPresentationAdd_one
  map_mul' := gammaGroundRVDirectSumToPresentationAdd_mul

@[simp] theorem gammaGroundRVDirectSumToPresentation_class {k : ℕ} (U : GammaGroundRVObject hc ground k) :
    gammaGroundRVDirectSumToPresentation (gammaGroundRVDirectSumClass U) = gammaGroundRVSemiringClass U :=
  (gammaGroundRVDirectSumToPresentationAdd_of k (gammaGroundRVClass U)).trans (gammaGroundRVKPlusToSemiring_class U)

def gammaGroundRVSemiringEquivDirectSum : GammaGroundRVPositiveSemiring hc ground ≃+* GammaGroundRVDirectSum hc ground := by
  let F := gammaGroundRVPresentationToDirectSum (M := M) (hc := hc) (ground := ground)
  let B := gammaGroundRVDirectSumToPresentation (M := M) (hc := hc) (ground := ground)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaGroundRVSemiringPresentation hc ground)
    rintro ⟨k, U⟩
    change B (F (gammaGroundRVSemiringClass U)) = gammaGroundRVSemiringClass U
    rw [gammaGroundRVPresentationToDirectSum_class, gammaGroundRVDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
      change F (B (gammaGroundRVDirectSumClass U)) = gammaGroundRVDirectSumClass U
      rw [gammaGroundRVDirectSumToPresentation_class, gammaGroundRVPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
