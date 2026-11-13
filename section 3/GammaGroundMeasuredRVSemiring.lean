import «section 3».GammaGroundMeasuredRVProducts
import Section4.PositivePresentation

/-! The cartesian universal presentation uses the actual pointwise
measured RV groupoids and full Gamma forms in every degree. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def GammaGroundMeasuredRVObject.withZeroForm (U : GammaGroundRVObject hc ground k) : GammaGroundMeasuredRVObject hc ground k :=
  ⟨U, gammaGroundOneForm U.domain⟩

def GammaGroundMeasuredRVObject.unit (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundMeasuredRVObject hc ground 0 :=
  .withZeroForm (GammaGroundRVObject.unit hc ground)

abbrev GradedGammaGroundMeasuredRVObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := Σ k, GammaGroundMeasuredRVObject hc ground k

def gradedGammaGroundMeasuredRVIso (A B : GradedGammaGroundMeasuredRVObject hc ground) : Prop :=
  ∃ k, ∃ a b : GammaGroundMeasuredRVObject hc ground k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedGammaGroundMeasuredRVScissor (A B D E : GradedGammaGroundMeasuredRVObject hc ground) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundMeasuredRVObject hc ground k,
    gammaGroundMeasuredRVScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundMeasuredRVObject.empty hc ground k⟩ ∧ B = ⟨0, GammaGroundMeasuredRVObject.empty hc ground 0⟩ ∧
    D = ⟨0, GammaGroundMeasuredRVObject.empty hc ground 0⟩ ∧ E = ⟨0, GammaGroundMeasuredRVObject.empty hc ground 0⟩)

def gammaGroundMeasuredRVSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : PositiveGrothendieck.Presentation (GradedGammaGroundMeasuredRVObject hc ground) where
  iso := gradedGammaGroundMeasuredRVIso
  empty := ⟨0, GammaGroundMeasuredRVObject.empty hc ground 0⟩
  unit := ⟨0, GammaGroundMeasuredRVObject.unit hc ground⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedGammaGroundMeasuredRVScissor

abbrev GammaGroundMeasuredRVPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := PositiveGrothendieck.KPlus (gammaGroundMeasuredRVSemiringPresentation hc ground)

abbrev GammaGroundMeasuredRVGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVPositiveSemiring hc ground)

def gammaGroundMeasuredRVSemiringClass (U : GammaGroundMeasuredRVObject hc ground k) : GammaGroundMeasuredRVPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundMeasuredRVSemiringPresentation hc ground) ⟨k, U⟩

theorem gammaGroundMeasuredRVSemiringClass_iso {U V : GammaGroundMeasuredRVObject hc ground k} (e : U ≅ V) :
    gammaGroundMeasuredRVSemiringClass U = gammaGroundMeasuredRVSemiringClass V :=
  PositiveGrothendieck.of_iso (gammaGroundMeasuredRVSemiringPresentation hc ground) ⟨k, U, V, ⟨e⟩, rfl, rfl⟩

@[simp] theorem gammaGroundMeasuredRVSemiringClass_empty :
    gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.empty hc ground k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundMeasuredRVSemiringPresentation (M := M) hc ground)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundMeasuredRVSemiringPresentation (M := M) hc ground)
      ⟨0, GammaGroundMeasuredRVObject.empty hc ground 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundMeasuredRVSemiringClass_unit :
    gammaGroundMeasuredRVSemiringClass (GammaGroundMeasuredRVObject.unit hc ground) = 1 := PositiveGrothendieck.of_unit _

theorem gammaGroundMeasuredRVSemiringClass_product (U : GammaGroundMeasuredRVObject hc ground k)
    (V : GammaGroundMeasuredRVObject hc ground l) :
    gammaGroundMeasuredRVSemiringClass (U.product V) = gammaGroundMeasuredRVSemiringClass U * gammaGroundMeasuredRVSemiringClass V :=
  PositiveGrothendieck.of_product (gammaGroundMeasuredRVSemiringPresentation hc ground) ⟨k, U⟩ ⟨l, V⟩

theorem gammaGroundMeasuredRVSemiringClass_scissor {A B D E : GammaGroundMeasuredRVObject hc ground k}
    (h : gammaGroundMeasuredRVScissor A B D E) :
    gammaGroundMeasuredRVSemiringClass A + gammaGroundMeasuredRVSemiringClass B =
      gammaGroundMeasuredRVSemiringClass D + gammaGroundMeasuredRVSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundMeasuredRVSemiringPresentation hc ground)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundMeasuredRVKPlusToSemiring : GammaGroundMeasuredRVKPlus hc ground k →+ GammaGroundMeasuredRVPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredRVPresentation hc ground k) {
    toFun := gammaGroundMeasuredRVSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundMeasuredRVSemiringClass_iso e
    empty := gammaGroundMeasuredRVSemiringClass_empty
    scissor := gammaGroundMeasuredRVSemiringClass_scissor }

@[simp] theorem gammaGroundMeasuredRVKPlusToSemiring_class (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVKPlusToSemiring (gammaGroundMeasuredRVClass U) = gammaGroundMeasuredRVSemiringClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

end DiamondIntegral.Section3
