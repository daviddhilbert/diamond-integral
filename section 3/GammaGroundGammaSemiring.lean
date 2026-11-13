import Section4.PositivePresentation
import «section 3».GammaGroundGammaProducts
/-! The Gamma positive semiring is presented by the actual tagged
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

abbrev GammaGroundGradedGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Σ k, GammaGroundGammaObject hc ground k

def gammaGroundGradedGammaIso (A B : GammaGroundGradedGammaObject hc ground) : Prop :=
  ∃ k, ∃ a b : GammaGroundGammaObject hc ground k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gammaGroundGradedGammaScissor (A B D E : GammaGroundGradedGammaObject hc ground) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundGammaObject hc ground k,
    GammaGroundGammaScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundGammaObject.empty hc ground k⟩ ∧ B = ⟨0, GammaGroundGammaObject.empty hc ground 0⟩ ∧
    D = ⟨0, GammaGroundGammaObject.empty hc ground 0⟩ ∧ E = ⟨0, GammaGroundGammaObject.empty hc ground 0⟩)

def gammaGroundGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    PositiveGrothendieck.Presentation (GammaGroundGradedGammaObject (M := M) hc ground) where
  iso := gammaGroundGradedGammaIso
  empty := ⟨0, GammaGroundGammaObject.empty hc ground 0⟩
  unit := ⟨0, GammaGroundGammaObject.unit hc ground⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gammaGroundGradedGammaScissor

abbrev GammaGroundGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  PositiveGrothendieck.KPlus (gammaGroundGammaSemiringPresentation (M := M) hc ground)
abbrev GammaGroundGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Algebra.GrothendieckAddGroup (GammaGroundGammaPositiveSemiring (M := M) hc ground)

def gammaGroundGammaSemiringClass (A : GammaGroundGammaObject hc ground k) : GammaGroundGammaPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundGammaSemiringPresentation hc ground) ⟨k, A⟩

theorem gammaGroundGammaSemiringClass_iso {A B : GammaGroundGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundGammaSemiringClass A = gammaGroundGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (gammaGroundGammaSemiringPresentation hc ground) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem gammaGroundGammaSemiringClass_empty : gammaGroundGammaSemiringClass (GammaGroundGammaObject.empty hc ground k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundGammaSemiringPresentation (M := M) hc ground)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundGammaSemiringPresentation (M := M) hc ground)
      ⟨0, GammaGroundGammaObject.empty hc ground 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundGammaSemiringClass_unit : gammaGroundGammaSemiringClass (GammaGroundGammaObject.unit hc ground) = 1 :=
  PositiveGrothendieck.of_unit (gammaGroundGammaSemiringPresentation hc ground)

theorem gammaGroundGammaSemiringClass_product (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l) :
    gammaGroundGammaSemiringClass (A.product B) = gammaGroundGammaSemiringClass A * gammaGroundGammaSemiringClass B :=
  PositiveGrothendieck.of_product (gammaGroundGammaSemiringPresentation hc ground) ⟨k, A⟩ ⟨l, B⟩

theorem gammaGroundGammaSemiringClass_scissor {A B D E : GammaGroundGammaObject hc ground k} (h : GammaGroundGammaScissor A B D E) :
    gammaGroundGammaSemiringClass A + gammaGroundGammaSemiringClass B = gammaGroundGammaSemiringClass D + gammaGroundGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundGammaSemiringPresentation hc ground)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundGammaKPlusToSemiring : GammaGroundGammaKPlus hc ground k →+ GammaGroundGammaPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundGammaPresentation hc ground k) {
    toFun := gammaGroundGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundGammaSemiringClass_iso e
    empty := gammaGroundGammaSemiringClass_empty
    scissor := gammaGroundGammaSemiringClass_scissor }

@[simp] theorem gammaGroundGammaKPlusToSemiring_class (A : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaKPlusToSemiring (gammaGroundGammaClass A) = gammaGroundGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
