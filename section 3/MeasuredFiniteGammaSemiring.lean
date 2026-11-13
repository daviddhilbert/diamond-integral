import «section 3».MeasuredGammaProducts
import «section 3».MeasuredFiniteGammaScissors
import Section4.PositivePresentation

/-! The finite measured Gamma positive semiring is presented by the actual tagged
objects, genuine contraction arrows, scissors and cartesian products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

abbrev GradedMeasuredFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Σ k, MeasuredFiniteGammaObject hc S k

def gradedMeasuredFiniteGammaIso (A B : GradedMeasuredFiniteGammaObject hc S) : Prop :=
  ∃ k, ∃ a b : MeasuredFiniteGammaObject hc S k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedMeasuredFiniteGammaScissor (A B D E : GradedMeasuredFiniteGammaObject hc S) : Prop :=
  (∃ k, ∃ a b d e : MeasuredFiniteGammaObject hc S k,
    MeasuredGammaScissor a.obj b.obj d.obj e.obj ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, MeasuredFiniteGammaObject.empty hc S k⟩ ∧ B = ⟨0, MeasuredFiniteGammaObject.empty hc S 0⟩ ∧
    D = ⟨0, MeasuredFiniteGammaObject.empty hc S 0⟩ ∧ E = ⟨0, MeasuredFiniteGammaObject.empty hc S 0⟩)

def measuredFiniteGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    PositiveGrothendieck.Presentation (GradedMeasuredFiniteGammaObject (M := M) hc S) where
  iso := gradedMeasuredFiniteGammaIso
  empty := ⟨0, MeasuredFiniteGammaObject.empty hc S 0⟩
  unit := ⟨0, MeasuredFiniteGammaObject.unit hc S⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedMeasuredFiniteGammaScissor

abbrev MeasuredFiniteGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  PositiveGrothendieck.KPlus (measuredFiniteGammaSemiringPresentation (M := M) hc S)
abbrev MeasuredFiniteGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Algebra.GrothendieckAddGroup (MeasuredFiniteGammaPositiveSemiring (M := M) hc S)

def measuredFiniteGammaSemiringClass (A : MeasuredFiniteGammaObject hc S k) : MeasuredFiniteGammaPositiveSemiring hc S :=
  PositiveGrothendieck.of (measuredFiniteGammaSemiringPresentation hc S) ⟨k, A⟩

theorem measuredFiniteGammaSemiringClass_iso {A B : MeasuredFiniteGammaObject hc S k} (e : A ≅ B) :
    measuredFiniteGammaSemiringClass A = measuredFiniteGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (measuredFiniteGammaSemiringPresentation hc S) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem measuredFiniteGammaSemiringClass_empty : measuredFiniteGammaSemiringClass (MeasuredFiniteGammaObject.empty hc S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (measuredFiniteGammaSemiringPresentation (M := M) hc S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (measuredFiniteGammaSemiringPresentation (M := M) hc S)
      ⟨0, MeasuredFiniteGammaObject.empty hc S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem measuredFiniteGammaSemiringClass_unit : measuredFiniteGammaSemiringClass (MeasuredFiniteGammaObject.unit hc S) = 1 :=
  PositiveGrothendieck.of_unit (measuredFiniteGammaSemiringPresentation hc S)

theorem measuredFiniteGammaSemiringClass_product (A : MeasuredFiniteGammaObject hc S k) (B : MeasuredFiniteGammaObject hc S l) :
    measuredFiniteGammaSemiringClass (A.product B) = measuredFiniteGammaSemiringClass A * measuredFiniteGammaSemiringClass B :=
  PositiveGrothendieck.of_product (measuredFiniteGammaSemiringPresentation hc S) ⟨k, A⟩ ⟨l, B⟩

theorem measuredFiniteGammaSemiringClass_scissor {A B D E : MeasuredFiniteGammaObject hc S k} (h : MeasuredGammaScissor A.obj B.obj D.obj E.obj) :
    measuredFiniteGammaSemiringClass A + measuredFiniteGammaSemiringClass B = measuredFiniteGammaSemiringClass D + measuredFiniteGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (measuredFiniteGammaSemiringPresentation hc S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def measuredFiniteGammaKPlusToSemiring : MeasuredFiniteGammaKPlus hc S k →+ MeasuredFiniteGammaPositiveSemiring hc S :=
  PositiveAdditiveGrothendieck.lift (measuredFiniteGammaPresentation hc S k) {
    toFun := measuredFiniteGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact measuredFiniteGammaSemiringClass_iso e
    empty := measuredFiniteGammaSemiringClass_empty
    scissor := measuredFiniteGammaSemiringClass_scissor }

@[simp] theorem measuredFiniteGammaKPlusToSemiring_class (A : MeasuredFiniteGammaObject hc S k) :
    measuredFiniteGammaKPlusToSemiring (measuredFiniteGammaClass A) = measuredFiniteGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
