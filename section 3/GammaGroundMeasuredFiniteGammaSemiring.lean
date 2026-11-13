import Section4.PositivePresentation
import «section 3».GammaGroundMeasuredGammaProducts
import «section 3».GammaGroundMeasuredFiniteGammaScissors
/-! The finite measured Gamma positive semiring is presented by the actual tagged
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

abbrev GammaGroundGradedMeasuredFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Σ k, GammaGroundMeasuredFiniteGammaObject hc ground k

def gammaGroundGradedMeasuredFiniteGammaIso (A B : GammaGroundGradedMeasuredFiniteGammaObject hc ground) : Prop :=
  ∃ k, ∃ a b : GammaGroundMeasuredFiniteGammaObject hc ground k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gammaGroundGradedMeasuredFiniteGammaScissor (A B D E : GammaGroundGradedMeasuredFiniteGammaObject hc ground) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundMeasuredFiniteGammaObject hc ground k,
    GammaGroundMeasuredGammaScissor a.obj b.obj d.obj e.obj ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundMeasuredFiniteGammaObject.empty hc ground k⟩ ∧ B = ⟨0, GammaGroundMeasuredFiniteGammaObject.empty hc ground 0⟩ ∧
    D = ⟨0, GammaGroundMeasuredFiniteGammaObject.empty hc ground 0⟩ ∧ E = ⟨0, GammaGroundMeasuredFiniteGammaObject.empty hc ground 0⟩)

def gammaGroundMeasuredFiniteGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    PositiveGrothendieck.Presentation (GammaGroundGradedMeasuredFiniteGammaObject (M := M) hc ground) where
  iso := gammaGroundGradedMeasuredFiniteGammaIso
  empty := ⟨0, GammaGroundMeasuredFiniteGammaObject.empty hc ground 0⟩
  unit := ⟨0, GammaGroundMeasuredFiniteGammaObject.unit hc ground⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gammaGroundGradedMeasuredFiniteGammaScissor

abbrev GammaGroundMeasuredFiniteGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  PositiveGrothendieck.KPlus (gammaGroundMeasuredFiniteGammaSemiringPresentation (M := M) hc ground)
abbrev GammaGroundMeasuredFiniteGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Algebra.GrothendieckAddGroup (GammaGroundMeasuredFiniteGammaPositiveSemiring (M := M) hc ground)

def gammaGroundMeasuredFiniteGammaSemiringClass (A : GammaGroundMeasuredFiniteGammaObject hc ground k) : GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) ⟨k, A⟩

theorem gammaGroundMeasuredFiniteGammaSemiringClass_iso {A B : GammaGroundMeasuredFiniteGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundMeasuredFiniteGammaSemiringClass A = gammaGroundMeasuredFiniteGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem gammaGroundMeasuredFiniteGammaSemiringClass_empty : gammaGroundMeasuredFiniteGammaSemiringClass (GammaGroundMeasuredFiniteGammaObject.empty hc ground k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundMeasuredFiniteGammaSemiringPresentation (M := M) hc ground)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundMeasuredFiniteGammaSemiringPresentation (M := M) hc ground)
      ⟨0, GammaGroundMeasuredFiniteGammaObject.empty hc ground 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundMeasuredFiniteGammaSemiringClass_unit : gammaGroundMeasuredFiniteGammaSemiringClass (GammaGroundMeasuredFiniteGammaObject.unit hc ground) = 1 :=
  PositiveGrothendieck.of_unit (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground)

theorem gammaGroundMeasuredFiniteGammaSemiringClass_product (A : GammaGroundMeasuredFiniteGammaObject hc ground k) (B : GammaGroundMeasuredFiniteGammaObject hc ground l) :
    gammaGroundMeasuredFiniteGammaSemiringClass (A.product B) = gammaGroundMeasuredFiniteGammaSemiringClass A * gammaGroundMeasuredFiniteGammaSemiringClass B :=
  PositiveGrothendieck.of_product (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground) ⟨k, A⟩ ⟨l, B⟩

theorem gammaGroundMeasuredFiniteGammaSemiringClass_scissor {A B D E : GammaGroundMeasuredFiniteGammaObject hc ground k} (h : GammaGroundMeasuredGammaScissor A.obj B.obj D.obj E.obj) :
    gammaGroundMeasuredFiniteGammaSemiringClass A + gammaGroundMeasuredFiniteGammaSemiringClass B = gammaGroundMeasuredFiniteGammaSemiringClass D + gammaGroundMeasuredFiniteGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundMeasuredFiniteGammaSemiringPresentation hc ground)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundMeasuredFiniteGammaKPlusToSemiring : GammaGroundMeasuredFiniteGammaKPlus hc ground k →+ GammaGroundMeasuredFiniteGammaPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredFiniteGammaPresentation hc ground k) {
    toFun := gammaGroundMeasuredFiniteGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundMeasuredFiniteGammaSemiringClass_iso e
    empty := gammaGroundMeasuredFiniteGammaSemiringClass_empty
    scissor := gammaGroundMeasuredFiniteGammaSemiringClass_scissor }

@[simp] theorem gammaGroundMeasuredFiniteGammaKPlusToSemiring_class (A : GammaGroundMeasuredFiniteGammaObject hc ground k) :
    gammaGroundMeasuredFiniteGammaKPlusToSemiring (gammaGroundMeasuredFiniteGammaClass A) = gammaGroundMeasuredFiniteGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
