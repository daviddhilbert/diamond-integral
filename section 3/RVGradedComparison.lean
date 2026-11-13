import «section 3».RVGradedSemiring

/-! The universal semiring presentation is exactly the direct sum of
the genuine fixed-degree positive scissors. In particular, supplying
multiplication has introduced no unintended additive identifications. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rvDirectSumInvariant : PositiveGrothendieck.Invariant (rvSemiringPresentation (M := M) S)
    (R := RVDirectSum (M := M) S) where
  toFun A := rvDirectSumClass A.2
  iso := by
    rintro ⟨k, A⟩ ⟨l, B⟩ ⟨he, ⟨f⟩⟩
    change k = l at he
    subst l
    exact congrArg (DirectSum.of (RVKPlus S) k) (rvClass_iso (asIso (show A ⟶ B from f)))
  empty := by
    change DirectSum.of (RVKPlus S) 0 (rvClass (RVObject.empty S 0)) = 0
    rw [rvClass_empty, map_zero]
  unit := rfl
  product A B := rvDirectSumClass_product A.2 B.2
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change DirectSum.of (RVKPlus S) k (rvClass a) + DirectSum.of (RVKPlus S) k (rvClass b) =
        DirectSum.of (RVKPlus S) k (rvClass d) + DirectSum.of (RVKPlus S) k (rvClass e)
      rw [← map_add, ← map_add]
      exact congrArg (DirectSum.of (RVKPlus S) k) (positiveClass_scissor (rvPresentation S k) hs)
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [rvDirectSumClass, rvClass_empty, map_zero, add_zero]

def rvPresentationToDirectSum : RVPositiveSemiring (M := M) S →+* RVDirectSum S :=
  PositiveGrothendieck.lift (rvSemiringPresentation S) rvDirectSumInvariant

@[simp] theorem rvPresentationToDirectSum_class {k : ℕ} (U : RVObject (M := M) S k) :
    rvPresentationToDirectSum (rvSemiringClass U) = rvDirectSumClass U :=
  PositiveGrothendieck.lift_of (rvSemiringPresentation S)
    (rvDirectSumInvariant (M := M) (S := S)) ⟨k, U⟩

def rvDirectSumToPresentationAdd : RVDirectSum (M := M) S →+ RVPositiveSemiring S :=
  DirectSum.toAddMonoid (fun _ => rvKPlusToSemiring)

@[simp] theorem rvDirectSumToPresentationAdd_of (k : ℕ) (a : RVKPlus (M := M) S k) :
    rvDirectSumToPresentationAdd (DirectSum.of (RVKPlus S) k a) = rvKPlusToSemiring a :=
  DirectSum.toAddMonoid_of _ _ _

theorem rvDirectSumToPresentationAdd_one :
    rvDirectSumToPresentationAdd (1 : RVDirectSum (M := M) S) = 1 := by
  change rvDirectSumToPresentationAdd (DirectSum.of (RVKPlus S) 0 (rvClass (RVObject.unit S))) = 1
  rw [rvDirectSumToPresentationAdd_of, rvKPlusToSemiring_class, rvSemiringClass_unit]

theorem rvDirectSumToPresentationAdd_mul (a b : RVDirectSum (M := M) S) :
    rvDirectSumToPresentationAdd (a * b) =
      rvDirectSumToPresentationAdd a * rvDirectSumToPresentationAdd b := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | of j b =>
      obtain ⟨U, rfl⟩ := rvClass_surjective a
      obtain ⟨V, rfl⟩ := rvClass_surjective b
      rw [DirectSum.of_mul_of]
      change rvDirectSumToPresentationAdd
        (DirectSum.of (RVKPlus S) (i + j) (rvClassMul (rvClass U) (rvClass V))) = _
      rw [rvClassMul_class, rvDirectSumToPresentationAdd_of,
        rvDirectSumToPresentationAdd_of, rvDirectSumToPresentationAdd_of,
        rvKPlusToSemiring_class, rvKPlusToSemiring_class, rvKPlusToSemiring_class,
        rvSemiringClass_product]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, ha, hc]

def rvDirectSumToPresentation : RVDirectSum (M := M) S →+* RVPositiveSemiring S where
  __ := rvDirectSumToPresentationAdd
  map_one' := rvDirectSumToPresentationAdd_one
  map_mul' := rvDirectSumToPresentationAdd_mul

@[simp] theorem rvDirectSumToPresentation_class {k : ℕ} (U : RVObject (M := M) S k) :
    rvDirectSumToPresentation (rvDirectSumClass U) = rvSemiringClass U :=
  (rvDirectSumToPresentationAdd_of k (rvClass U)).trans (rvKPlusToSemiring_class U)

def rvSemiringEquivDirectSum : RVPositiveSemiring (M := M) S ≃+* RVDirectSum S := by
  let F := rvPresentationToDirectSum (M := M) (S := S)
  let B := rvDirectSumToPresentation (M := M) (S := S)
  have hBF : B.comp F = RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (rvSemiringPresentation S)
    rintro ⟨k, U⟩
    change B (F (rvSemiringClass U)) = rvSemiringClass U
    rw [rvPresentationToDirectSum_class, rvDirectSumToPresentation_class]
  have hFB : F.comp B = RingHom.id _ := by
    apply RingHom.ext
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp only [map_zero, RingHom.comp_apply, RingHom.id_apply]
    | of k a =>
      obtain ⟨U, rfl⟩ := rvClass_surjective a
      change F (B (rvDirectSumClass U)) = rvDirectSumClass U
      rw [rvDirectSumToPresentation_class, rvPresentationToDirectSum_class]
    | add a b ha hb => simpa only [map_add, RingHom.comp_apply, RingHom.id_apply] using congrArg₂ (· + ·) ha hb
  exact RingEquiv.ofRingHom F B hFB hBF

end DiamondIntegral.Section3
