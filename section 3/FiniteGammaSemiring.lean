import «section 3».GammaProducts
import «section 3».FiniteGammaScissors
import Section4.PositivePresentation

/-! The finite Gamma positive semiring is presented by the actual tagged
objects, genuine contraction arrows, scissors and cartesian products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

abbrev GradedFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Σ k, FiniteGammaObject hc S k

def gradedFiniteGammaIso (A B : GradedFiniteGammaObject hc S) : Prop :=
  ∃ k, ∃ a b : FiniteGammaObject hc S k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedFiniteGammaScissor (A B D E : GradedFiniteGammaObject hc S) : Prop :=
  (∃ k, ∃ a b d e : FiniteGammaObject hc S k,
    GammaScissor a.obj b.obj d.obj e.obj ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, FiniteGammaObject.empty hc S k⟩ ∧ B = ⟨0, FiniteGammaObject.empty hc S 0⟩ ∧
    D = ⟨0, FiniteGammaObject.empty hc S 0⟩ ∧ E = ⟨0, FiniteGammaObject.empty hc S 0⟩)

def finiteGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    PositiveGrothendieck.Presentation (GradedFiniteGammaObject (M := M) hc S) where
  iso := gradedFiniteGammaIso
  empty := ⟨0, FiniteGammaObject.empty hc S 0⟩
  unit := ⟨0, FiniteGammaObject.unit hc S⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedFiniteGammaScissor

abbrev FiniteGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  PositiveGrothendieck.KPlus (finiteGammaSemiringPresentation (M := M) hc S)
abbrev FiniteGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Algebra.GrothendieckAddGroup (FiniteGammaPositiveSemiring (M := M) hc S)

def finiteGammaSemiringClass (A : FiniteGammaObject hc S k) : FiniteGammaPositiveSemiring hc S :=
  PositiveGrothendieck.of (finiteGammaSemiringPresentation hc S) ⟨k, A⟩

theorem finiteGammaSemiringClass_iso {A B : FiniteGammaObject hc S k} (e : A ≅ B) :
    finiteGammaSemiringClass A = finiteGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (finiteGammaSemiringPresentation hc S) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem finiteGammaSemiringClass_empty : finiteGammaSemiringClass (FiniteGammaObject.empty hc S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (finiteGammaSemiringPresentation (M := M) hc S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (finiteGammaSemiringPresentation (M := M) hc S)
      ⟨0, FiniteGammaObject.empty hc S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem finiteGammaSemiringClass_unit : finiteGammaSemiringClass (FiniteGammaObject.unit hc S) = 1 :=
  PositiveGrothendieck.of_unit (finiteGammaSemiringPresentation hc S)

theorem finiteGammaSemiringClass_product (A : FiniteGammaObject hc S k) (B : FiniteGammaObject hc S l) :
    finiteGammaSemiringClass (A.product B) = finiteGammaSemiringClass A * finiteGammaSemiringClass B :=
  PositiveGrothendieck.of_product (finiteGammaSemiringPresentation hc S) ⟨k, A⟩ ⟨l, B⟩

theorem finiteGammaSemiringClass_scissor {A B D E : FiniteGammaObject hc S k} (h : GammaScissor A.obj B.obj D.obj E.obj) :
    finiteGammaSemiringClass A + finiteGammaSemiringClass B = finiteGammaSemiringClass D + finiteGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (finiteGammaSemiringPresentation hc S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def finiteGammaKPlusToSemiring : FiniteGammaKPlus hc S k →+ FiniteGammaPositiveSemiring hc S :=
  PositiveAdditiveGrothendieck.lift (finiteGammaPresentation hc S k) {
    toFun := finiteGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact finiteGammaSemiringClass_iso e
    empty := finiteGammaSemiringClass_empty
    scissor := finiteGammaSemiringClass_scissor }

@[simp] theorem finiteGammaKPlusToSemiring_class (A : FiniteGammaObject hc S k) :
    finiteGammaKPlusToSemiring (finiteGammaClass A) = finiteGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
