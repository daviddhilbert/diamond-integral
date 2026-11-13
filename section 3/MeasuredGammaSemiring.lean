import «section 3».MeasuredGammaProducts
import «section 3».GammaScissors
import Section4.PositivePresentation

/-! The measured Gamma positive semiring is presented by the actual tagged
objects, genuine contraction arrows, scissors and cartesian products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

abbrev GradedMeasuredGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Σ k, MeasuredGammaObject hc S k

def gradedMeasuredGammaIso (A B : GradedMeasuredGammaObject hc S) : Prop :=
  ∃ k, ∃ a b : MeasuredGammaObject hc S k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedMeasuredGammaScissor (A B D E : GradedMeasuredGammaObject hc S) : Prop :=
  (∃ k, ∃ a b d e : MeasuredGammaObject hc S k,
    MeasuredGammaScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, MeasuredGammaObject.empty hc S k⟩ ∧ B = ⟨0, MeasuredGammaObject.empty hc S 0⟩ ∧
    D = ⟨0, MeasuredGammaObject.empty hc S 0⟩ ∧ E = ⟨0, MeasuredGammaObject.empty hc S 0⟩)

def measuredGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    PositiveGrothendieck.Presentation (GradedMeasuredGammaObject (M := M) hc S) where
  iso := gradedMeasuredGammaIso
  empty := ⟨0, MeasuredGammaObject.empty hc S 0⟩
  unit := ⟨0, MeasuredGammaObject.unit hc S⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedMeasuredGammaScissor

abbrev MeasuredGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  PositiveGrothendieck.KPlus (measuredGammaSemiringPresentation (M := M) hc S)
abbrev MeasuredGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Algebra.GrothendieckAddGroup (MeasuredGammaPositiveSemiring (M := M) hc S)

def measuredGammaSemiringClass (A : MeasuredGammaObject hc S k) : MeasuredGammaPositiveSemiring hc S :=
  PositiveGrothendieck.of (measuredGammaSemiringPresentation hc S) ⟨k, A⟩

theorem measuredGammaSemiringClass_iso {A B : MeasuredGammaObject hc S k} (e : A ≅ B) :
    measuredGammaSemiringClass A = measuredGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (measuredGammaSemiringPresentation hc S) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem measuredGammaSemiringClass_empty : measuredGammaSemiringClass (MeasuredGammaObject.empty hc S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (measuredGammaSemiringPresentation (M := M) hc S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (measuredGammaSemiringPresentation (M := M) hc S)
      ⟨0, MeasuredGammaObject.empty hc S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem measuredGammaSemiringClass_unit : measuredGammaSemiringClass (MeasuredGammaObject.unit hc S) = 1 :=
  PositiveGrothendieck.of_unit (measuredGammaSemiringPresentation hc S)

theorem measuredGammaSemiringClass_product (A : MeasuredGammaObject hc S k) (B : MeasuredGammaObject hc S l) :
    measuredGammaSemiringClass (A.product B) = measuredGammaSemiringClass A * measuredGammaSemiringClass B :=
  PositiveGrothendieck.of_product (measuredGammaSemiringPresentation hc S) ⟨k, A⟩ ⟨l, B⟩

theorem measuredGammaSemiringClass_scissor {A B D E : MeasuredGammaObject hc S k} (h : MeasuredGammaScissor A B D E) :
    measuredGammaSemiringClass A + measuredGammaSemiringClass B = measuredGammaSemiringClass D + measuredGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (measuredGammaSemiringPresentation hc S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def measuredGammaKPlusToSemiring : MeasuredGammaKPlus hc S k →+ MeasuredGammaPositiveSemiring hc S :=
  PositiveAdditiveGrothendieck.lift (measuredGammaPresentation hc S k) {
    toFun := measuredGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact measuredGammaSemiringClass_iso e
    empty := measuredGammaSemiringClass_empty
    scissor := measuredGammaSemiringClass_scissor }

@[simp] theorem measuredGammaKPlusToSemiring_class (A : MeasuredGammaObject hc S k) :
    measuredGammaKPlusToSemiring (measuredGammaClass A) = measuredGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
