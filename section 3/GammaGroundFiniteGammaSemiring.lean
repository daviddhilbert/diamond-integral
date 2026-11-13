import Section4.PositivePresentation
import «section 3».GammaGroundGammaProducts
import «section 3».GammaGroundFiniteGammaScissors
/-! The finite Gamma positive semiring is presented by the actual tagged
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

abbrev GammaGroundGradedFiniteGammaObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Σ k, GammaGroundFiniteGammaObject hc ground k

def gammaGroundGradedFiniteGammaIso (A B : GammaGroundGradedFiniteGammaObject hc ground) : Prop :=
  ∃ k, ∃ a b : GammaGroundFiniteGammaObject hc ground k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gammaGroundGradedFiniteGammaScissor (A B D E : GammaGroundGradedFiniteGammaObject hc ground) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundFiniteGammaObject hc ground k,
    GammaGroundGammaScissor a.obj b.obj d.obj e.obj ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundFiniteGammaObject.empty hc ground k⟩ ∧ B = ⟨0, GammaGroundFiniteGammaObject.empty hc ground 0⟩ ∧
    D = ⟨0, GammaGroundFiniteGammaObject.empty hc ground 0⟩ ∧ E = ⟨0, GammaGroundFiniteGammaObject.empty hc ground 0⟩)

def gammaGroundFiniteGammaSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    PositiveGrothendieck.Presentation (GammaGroundGradedFiniteGammaObject (M := M) hc ground) where
  iso := gammaGroundGradedFiniteGammaIso
  empty := ⟨0, GammaGroundFiniteGammaObject.empty hc ground 0⟩
  unit := ⟨0, GammaGroundFiniteGammaObject.unit hc ground⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gammaGroundGradedFiniteGammaScissor

abbrev GammaGroundFiniteGammaPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  PositiveGrothendieck.KPlus (gammaGroundFiniteGammaSemiringPresentation (M := M) hc ground)
abbrev GammaGroundFiniteGammaGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :=
  Algebra.GrothendieckAddGroup (GammaGroundFiniteGammaPositiveSemiring (M := M) hc ground)

def gammaGroundFiniteGammaSemiringClass (A : GammaGroundFiniteGammaObject hc ground k) : GammaGroundFiniteGammaPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundFiniteGammaSemiringPresentation hc ground) ⟨k, A⟩

theorem gammaGroundFiniteGammaSemiringClass_iso {A B : GammaGroundFiniteGammaObject hc ground k} (e : A ≅ B) :
    gammaGroundFiniteGammaSemiringClass A = gammaGroundFiniteGammaSemiringClass B :=
  PositiveGrothendieck.of_iso (gammaGroundFiniteGammaSemiringPresentation hc ground) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem gammaGroundFiniteGammaSemiringClass_empty : gammaGroundFiniteGammaSemiringClass (GammaGroundFiniteGammaObject.empty hc ground k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundFiniteGammaSemiringPresentation (M := M) hc ground)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundFiniteGammaSemiringPresentation (M := M) hc ground)
      ⟨0, GammaGroundFiniteGammaObject.empty hc ground 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundFiniteGammaSemiringClass_unit : gammaGroundFiniteGammaSemiringClass (GammaGroundFiniteGammaObject.unit hc ground) = 1 :=
  PositiveGrothendieck.of_unit (gammaGroundFiniteGammaSemiringPresentation hc ground)

theorem gammaGroundFiniteGammaSemiringClass_product (A : GammaGroundFiniteGammaObject hc ground k) (B : GammaGroundFiniteGammaObject hc ground l) :
    gammaGroundFiniteGammaSemiringClass (A.product B) = gammaGroundFiniteGammaSemiringClass A * gammaGroundFiniteGammaSemiringClass B :=
  PositiveGrothendieck.of_product (gammaGroundFiniteGammaSemiringPresentation hc ground) ⟨k, A⟩ ⟨l, B⟩

theorem gammaGroundFiniteGammaSemiringClass_scissor {A B D E : GammaGroundFiniteGammaObject hc ground k} (h : GammaGroundGammaScissor A.obj B.obj D.obj E.obj) :
    gammaGroundFiniteGammaSemiringClass A + gammaGroundFiniteGammaSemiringClass B = gammaGroundFiniteGammaSemiringClass D + gammaGroundFiniteGammaSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundFiniteGammaSemiringPresentation hc ground)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundFiniteGammaKPlusToSemiring : GammaGroundFiniteGammaKPlus hc ground k →+ GammaGroundFiniteGammaPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundFiniteGammaPresentation hc ground k) {
    toFun := gammaGroundFiniteGammaSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundFiniteGammaSemiringClass_iso e
    empty := gammaGroundFiniteGammaSemiringClass_empty
    scissor := gammaGroundFiniteGammaSemiringClass_scissor }

@[simp] theorem gammaGroundFiniteGammaKPlusToSemiring_class (A : GammaGroundFiniteGammaObject hc ground k) :
    gammaGroundFiniteGammaKPlusToSemiring (gammaGroundFiniteGammaClass A) = gammaGroundFiniteGammaSemiringClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
