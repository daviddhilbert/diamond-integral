import «section 3».MeasuredRESSemiring
import «section 3».MeasuredRVSemiring

/-! The measured RES inclusion is a genuine semiring homomorphism and
agrees with the fixed-degree additive forgetful maps. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

def measuredRESForgetInvariant :
    PositiveGrothendieck.Invariant (measuredRESSemiringPresentation (M := M) hc S)
      (R := MeasuredRVPositiveSemiring hc S) where
  toFun A := measuredRVSemiringClass hc A.2.obj
  iso := by
    rintro A B ⟨k, a, b, ⟨e⟩, rfl, rfl⟩
    exact measuredRVSemiringClass_iso hc ((measuredResProperty S k).ι.mapIso e)
  empty := measuredRVSemiringClass_empty hc
  unit := measuredRVSemiringClass_unit hc
  product A B := measuredRVSemiringClass_product hc A.2.obj B.2.obj
  scissor := by
    intro A B D E h
    rcases h with h | h
    · obtain ⟨k, a, b, d, e, hs, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      exact measuredRVSemiringClass_scissor hc hs
    · obtain ⟨k, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      simp only [MeasuredRESObject.empty, measuredRVSemiringClass_empty, add_zero]

def measuredRESForgetSemiring : MeasuredRESPositiveSemiring hc S →+* MeasuredRVPositiveSemiring hc S :=
  PositiveGrothendieck.lift (measuredRESSemiringPresentation hc S) measuredRESForgetInvariant

@[simp] theorem measuredRESForgetSemiring_class {k : ℕ} (U : MeasuredRESObject (M := M) S k) :
    measuredRESForgetSemiring (measuredRESSemiringClass hc U) = measuredRVSemiringClass hc U.obj :=
  PositiveGrothendieck.lift_of (measuredRESSemiringPresentation hc S)
    (measuredRESForgetInvariant (hc := hc) (S := S)) ⟨k, U⟩

theorem measuredRESForgetSemiring_fixed {k : ℕ} :
    (measuredRESForgetSemiring (M := M) (hc := hc) (S := S)).toAddMonoidHom.comp
        (measuredRESKPlusToSemiring hc (k := k)) =
      (measuredRVKPlusToSemiring hc).comp (measuredResToRVKPlus hc) := by
  apply PositiveAdditiveGrothendieck.hom_ext (measuredRESPresentation hc S k)
  intro U
  change measuredRESForgetSemiring (measuredRESKPlusToSemiring hc (measuredResClass hc U)) =
    measuredRVKPlusToSemiring hc (measuredResToRVKPlus hc (measuredResClass hc U))
  rw [measuredRESKPlusToSemiring_class, measuredRESForgetSemiring_class,
    measuredResToRVKPlus_class, measuredRVKPlusToSemiring_class]

end DiamondIntegral.Section3
