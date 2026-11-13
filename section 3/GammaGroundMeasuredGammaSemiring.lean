import Section4.PositivePresentation
import «section 3».GammaGroundMeasuredGammaProducts
import «section 3».GammaGroundGammaScissors
/-! The measured Gamma positive semiring is presented by the actual tagged
objects, genuine contraction arrows, scissors and cartesian products. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

abbrev GammaGroundGradedMeasuredGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Σ k, GammaGroundMeasuredGammaObject hc ground k

def gammaGroundGradedMeasuredGammaIso (A B : GammaGroundGradedMeasuredGammaObject hc ground) : Prop :=
  ∃ k, ∃ a b : GammaGroundMeasuredGammaObject hc ground k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gammaGroundGradedMeasuredGammaScissor (A B D E : GammaGroundGradedMeasuredGammaObject hc ground) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundMeasuredGammaObject hc ground k,
    GammaGroundMeasuredGammaScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundMeasuredGammaObject.empty hc ground k⟩ ∧ B = ⟨0, GammaGroundMeasuredGammaObject.empty hc ground 0⟩ ∧
    D = ⟨0, GammaGroundMeasuredGammaObject.empty hc ground 0⟩ ∧ E = ⟨0, GammaGroundMeasuredGammaObject.empty hc ground 0⟩)

def gammaGroundMeasuredGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    PositiveGrothendieck.Presentation (GammaGroundGradedMeasuredGammaObject (M := M) hc ground) where
  iso := gammaGroundGradedMeasuredGammaIso
  empty := ⟨0, GammaGroundMeasuredGammaObject.empty hc ground 0⟩
  unit := ⟨0, GammaGroundMeasuredGammaObject.unit hc ground⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gammaGroundGradedMeasuredGammaScissor

abbrev GammaGroundMeasuredGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  PositiveGrothendieck.KPlus (gammaGroundMeasuredGammaSemiringPresentation (M := M) hc ground)
abbrev GammaGroundMeasuredGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Algebra.GrothendieckAddGroup (GammaGroundMeasuredGammaPositiveSemiring (M := M) hc ground)

def gammaGroundMeasuredGammaSemiringClass (A : GammaGroundMeasuredGammaObject hc ground k) : GammaGroundMeasuredGammaPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundMeasuredGammaSemiringPresentation hc ground) ⟨k, A⟩

theorem gammaGroundMeasuredGammaSemiringClass_iso {A B : GammaGroundMeasuredGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundMeasuredGammaSemiringClass A = gammaGroundMeasuredGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (gammaGroundMeasuredGammaSemiringPresentation hc ground) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem gammaGroundMeasuredGammaSemiringClass_empty : gammaGroundMeasuredGammaSemiringClass (GammaGroundMeasuredGammaObject.empty hc ground k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundMeasuredGammaSemiringPresentation (M := M) hc ground)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundMeasuredGammaSemiringPresentation (M := M) hc ground)
      ⟨0, GammaGroundMeasuredGammaObject.empty hc ground 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundMeasuredGammaSemiringClass_unit : gammaGroundMeasuredGammaSemiringClass (GammaGroundMeasuredGammaObject.unit hc ground) = 1 :=
  PositiveGrothendieck.of_unit (gammaGroundMeasuredGammaSemiringPresentation hc ground)

theorem gammaGroundMeasuredGammaSemiringClass_product (A : GammaGroundMeasuredGammaObject hc ground k) (B : GammaGroundMeasuredGammaObject hc ground l) :
    gammaGroundMeasuredGammaSemiringClass (A.product B) = gammaGroundMeasuredGammaSemiringClass A * gammaGroundMeasuredGammaSemiringClass B :=
  PositiveGrothendieck.of_product (gammaGroundMeasuredGammaSemiringPresentation hc ground) ⟨k, A⟩ ⟨l, B⟩

theorem gammaGroundMeasuredGammaSemiringClass_scissor {A B D E : GammaGroundMeasuredGammaObject hc ground k} (h : GammaGroundMeasuredGammaScissor A B D E) :
    gammaGroundMeasuredGammaSemiringClass A + gammaGroundMeasuredGammaSemiringClass B = gammaGroundMeasuredGammaSemiringClass D + gammaGroundMeasuredGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundMeasuredGammaSemiringPresentation hc ground)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundMeasuredGammaKPlusToSemiring : GammaGroundMeasuredGammaKPlus hc ground k →+ GammaGroundMeasuredGammaPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredGammaPresentation hc ground k) {
    toFun := gammaGroundMeasuredGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundMeasuredGammaSemiringClass_iso e
    empty := gammaGroundMeasuredGammaSemiringClass_empty
    scissor := gammaGroundMeasuredGammaSemiringClass_scissor }

@[simp] theorem gammaGroundMeasuredGammaKPlusToSemiring_class (A : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaKPlusToSemiring (gammaGroundMeasuredGammaClass A) = gammaGroundMeasuredGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
