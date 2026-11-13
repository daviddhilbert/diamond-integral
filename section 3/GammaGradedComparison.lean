import «section 3».GammaGradedSemiring
import «section 3».GammaSemiring

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

def gammaDirectSumInvariant : PositiveGrothendieck.Invariant (gammaSemiringPresentation hc (M := M) S)
    (R := GammaDirectSum (M := M) hc S) where
  toFun A := gammaDirectSumClass hc A.2
  iso := by
    intro A B h
    obtain ⟨k, a, b, ⟨e⟩, rfl, rfl⟩ := h
    exact congrArg (DirectSum.of (GammaKPlus hc S) k) (gammaClass_iso e)
  empty := by
    change DirectSum.of (GammaKPlus hc S) 0 (gammaClass (GammaObject.empty hc S 0)) = 0
    rw [gammaClass_empty, map_zero]
  unit := rfl
  product A B := gammaDirectSumClass_product (hc := hc) A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (GammaKPlus hc S) k (gammaClass a) + DirectSum.of (GammaKPlus hc S) k (gammaClass b) =
        DirectSum.of (GammaKPlus hc S) k (gammaClass d) + DirectSum.of (GammaKPlus hc S) k (gammaClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (GammaKPlus hc S) k) (positiveClass_scissor (gammaPresentation hc S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [gammaDirectSumClass, gammaClass_empty, map_zero, add_zero]

def gammaPresentationToDirectSum : GammaPositiveSemiring (M := M) hc S →+* GammaDirectSum hc S :=
  PositiveGrothendieck.lift (gammaSemiringPresentation hc S) gammaDirectSumInvariant

@[simp] theorem gammaPresentationToDirectSum_class {k : ℕ} (U : GammaObject (M := M) hc S k) :
    gammaPresentationToDirectSum (gammaSemiringClass U) = gammaDirectSumClass hc U :=
  PositiveGrothendieck.lift_of (gammaSemiringPresentation hc S)
    (gammaDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def gammaDirectSumToPresentationAdd : GammaDirectSum (M := M) hc S →+ GammaPositiveSemiring hc S :=
  DirectSum.toAddMonoid (fun _ => gammaKPlusToSemiring)

@[simp] theorem gammaDirectSumToPresentationAdd_of (k : ℕ) (a : GammaKPlus (M := M) hc S k) :
    gammaDirectSumToPresentationAdd (DirectSum.of (GammaKPlus hc S) k a) = gammaKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem gammaDirectSumToPresentationAdd_one :
    gammaDirectSumToPresentationAdd (1 : GammaDirectSum (M := M) hc S) = 1 := by
  change gammaDirectSumToPresentationAdd (DirectSum.of (GammaKPlus hc S) 0 (gammaClass (GammaObject.unit hc S))) = 1
  rw [gammaDirectSumToPresentationAdd_of, gammaKPlusToSemiring_class, gammaSemiringClass_unit]

theorem gammaDirectSumToPresentationAdd_mul (a b : GammaDirectSum (M := M) hc S) :
    gammaDirectSumToPresentationAdd (a * b) =
      gammaDirectSumToPresentationAdd a * gammaDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := gammaClass_surjective a
      obtain ⟨V, rfl⟩ := gammaClass_surjective b
      rw [DirectSum.of_mul_of]
      change gammaDirectSumToPresentationAdd
        (DirectSum.of (GammaKPlus hc S) (i + j) (gammaClassMul (gammaClass U) (gammaClass V))) = _
      rw [gammaClassMul_class, gammaDirectSumToPresentationAdd_of,
        gammaDirectSumToPresentationAdd_of, gammaDirectSumToPresentationAdd_of,
        gammaKPlusToSemiring_class, gammaKPlusToSemiring_class, gammaKPlusToSemiring_class,
        gammaSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def gammaDirectSumToPresentation : GammaDirectSum (M := M) hc S →+* GammaPositiveSemiring hc S where
  __ := gammaDirectSumToPresentationAdd
  map_one' := gammaDirectSumToPresentationAdd_one
  map_mul' := gammaDirectSumToPresentationAdd_mul

@[simp] theorem gammaDirectSumToPresentation_class {k : ℕ} (U : GammaObject (M := M) hc S k) :
    gammaDirectSumToPresentation (gammaDirectSumClass hc U) = gammaSemiringClass U :=
  (gammaDirectSumToPresentationAdd_of k (gammaClass U)).trans (gammaKPlusToSemiring_class U)

def gammaSemiringEquivDirectSum : GammaPositiveSemiring (M := M) hc S ≃+* GammaDirectSum hc S := by
  let F := gammaPresentationToDirectSum (M := M) (S := S) (hc := hc)
  let B := gammaDirectSumToPresentation (M := M) (S := S) (hc := hc)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaSemiringPresentation hc S)
    rintro ⟨k, U⟩
    change B (F (gammaSemiringClass U)) = gammaSemiringClass U
    rw [gammaPresentationToDirectSum_class, gammaDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := gammaClass_surjective a
      change F (B (gammaDirectSumClass hc U)) = gammaDirectSumClass hc U
      rw [gammaDirectSumToPresentation_class, gammaPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
