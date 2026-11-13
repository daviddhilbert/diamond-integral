import «section 3».GammaProducts
import Section4.PositivePresentation

/-! The Gamma positive semiring is presented by the actual tagged
objects, genuine contraction arrows, scissors and cartesian products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

abbrev GradedGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Σ k, GammaObject hc S k

def gradedGammaIso (A B : GradedGammaObject hc S) : Prop :=
  ∃ k, ∃ a b : GammaObject hc S k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedGammaScissor (A B D E : GradedGammaObject hc S) : Prop :=
  (∃ k, ∃ a b d e : GammaObject hc S k,
    GammaScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaObject.empty hc S k⟩ ∧ B = ⟨0, GammaObject.empty hc S 0⟩ ∧
    D = ⟨0, GammaObject.empty hc S 0⟩ ∧ E = ⟨0, GammaObject.empty hc S 0⟩)

def gammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    PositiveGrothendieck.Presentation (GradedGammaObject (M := M) hc S) where
  iso := gradedGammaIso
  empty := ⟨0, GammaObject.empty hc S 0⟩
  unit := ⟨0, GammaObject.unit hc S⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedGammaScissor

abbrev GammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  PositiveGrothendieck.KPlus (gammaSemiringPresentation (M := M) hc S)
abbrev GammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Algebra.GrothendieckAddGroup (GammaPositiveSemiring (M := M) hc S)

def gammaSemiringClass (A : GammaObject hc S k) : GammaPositiveSemiring hc S :=
  PositiveGrothendieck.of (gammaSemiringPresentation hc S) ⟨k, A⟩

theorem gammaSemiringClass_iso {A B : GammaObject hc S k} (e : A ≅ B) :
    gammaSemiringClass A = gammaSemiringClass B :=
  PositiveGrothendieck.of_iso (gammaSemiringPresentation hc S) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem gammaSemiringClass_empty : gammaSemiringClass (GammaObject.empty hc S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaSemiringPresentation (M := M) hc S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaSemiringPresentation (M := M) hc S)
      ⟨0, GammaObject.empty hc S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaSemiringClass_unit : gammaSemiringClass (GammaObject.unit hc S) = 1 :=
  PositiveGrothendieck.of_unit (gammaSemiringPresentation hc S)

theorem gammaSemiringClass_product (A : GammaObject hc S k) (B : GammaObject hc S l) :
    gammaSemiringClass (A.product B) = gammaSemiringClass A * gammaSemiringClass B :=
  PositiveGrothendieck.of_product (gammaSemiringPresentation hc S) ⟨k, A⟩ ⟨l, B⟩

theorem gammaSemiringClass_scissor {A B D E : GammaObject hc S k} (h : GammaScissor A B D E) :
    gammaSemiringClass A + gammaSemiringClass B = gammaSemiringClass D + gammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaSemiringPresentation hc S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaKPlusToSemiring : GammaKPlus hc S k →+ GammaPositiveSemiring hc S :=
  PositiveAdditiveGrothendieck.lift (gammaPresentation hc S k) {
    toFun := gammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaSemiringClass_iso e
    empty := gammaSemiringClass_empty
    scissor := gammaSemiringClass_scissor }

@[simp] theorem gammaKPlusToSemiring_class (A : GammaObject hc S k) :
    gammaKPlusToSemiring (gammaClass A) = gammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
