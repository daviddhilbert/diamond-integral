import «section 3».MeasuredRVProducts
import «section 3».MeasuredRVScissors
import Section4.PositivePresentation

/-! The universal measured RV positive semiring uses actual pointwise
Gamma-preserving arrows, inherited scissors and product volume forms. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

abbrev GradedMeasuredRVObject (S : Set M) := Σ k, MeasuredRVObject (M := M) S k

def gradedMeasuredRVIso (A B : GradedMeasuredRVObject (M := M) S) : Prop :=
  ∃ k, ∃ a b : MeasuredRVObject S k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedMeasuredRVScissor (hc : CanonicalStructure.IsCanonical (M := M))
    (A B D E : GradedMeasuredRVObject (M := M) S) : Prop :=
  (∃ k, ∃ a b d e : MeasuredRVObject S k,
    MeasuredRVScissor hc a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, MeasuredRVObject.empty S k⟩ ∧ B = ⟨0, MeasuredRVObject.empty S 0⟩ ∧
    D = ⟨0, MeasuredRVObject.empty S 0⟩ ∧ E = ⟨0, MeasuredRVObject.empty S 0⟩)

def measuredRVSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    PositiveGrothendieck.Presentation (GradedMeasuredRVObject (M := M) S) where
  iso := gradedMeasuredRVIso
  empty := ⟨0, MeasuredRVObject.empty S 0⟩
  unit := ⟨0, MeasuredRVObject.unit hc S⟩
  product A B := ⟨A.1 + B.1, A.2.product hc B.2⟩
  scissor := gradedMeasuredRVScissor hc

abbrev MeasuredRVPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  PositiveGrothendieck.KPlus (measuredRVSemiringPresentation (M := M) hc S)
abbrev MeasuredRVGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Algebra.GrothendieckAddGroup (MeasuredRVPositiveSemiring (M := M) hc S)

def measuredRVSemiringClass (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) : MeasuredRVPositiveSemiring hc S :=
  PositiveGrothendieck.of (measuredRVSemiringPresentation hc S) ⟨k, U⟩

theorem measuredRVSemiringClass_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S k} (e : U ≅ V) :
    measuredRVSemiringClass hc U = measuredRVSemiringClass hc V :=
  PositiveGrothendieck.of_iso (measuredRVSemiringPresentation hc S) ⟨k, U, V, ⟨e⟩, rfl, rfl⟩

@[simp] theorem measuredRVSemiringClass_empty (hc : CanonicalStructure.IsCanonical (M := M)) :
    measuredRVSemiringClass hc (MeasuredRVObject.empty (M := M) S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (measuredRVSemiringPresentation (M := M) hc S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (measuredRVSemiringPresentation (M := M) hc S)
      ⟨0, MeasuredRVObject.empty S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem measuredRVSemiringClass_unit (hc : CanonicalStructure.IsCanonical (M := M)) :
    measuredRVSemiringClass hc (MeasuredRVObject.unit (M := M) hc S) = 1 :=
  PositiveGrothendieck.of_unit (measuredRVSemiringPresentation hc S)

theorem measuredRVSemiringClass_product (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) (V : MeasuredRVObject (M := M) S l) :
    measuredRVSemiringClass hc (U.product hc V) =
      measuredRVSemiringClass hc U * measuredRVSemiringClass hc V :=
  PositiveGrothendieck.of_product (measuredRVSemiringPresentation hc S) ⟨k, U⟩ ⟨l, V⟩

theorem measuredRVSemiringClass_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    {A B D E : MeasuredRVObject (M := M) S k} (h : MeasuredRVScissor hc A B D E) :
    measuredRVSemiringClass hc A + measuredRVSemiringClass hc B =
      measuredRVSemiringClass hc D + measuredRVSemiringClass hc E :=
  PositiveGrothendieck.of_scissor (measuredRVSemiringPresentation hc S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def measuredRVKPlusToSemiring (hc : CanonicalStructure.IsCanonical (M := M)) :
    MeasuredRVKPlus hc S k →+ MeasuredRVPositiveSemiring hc S :=
  PositiveAdditiveGrothendieck.lift (measuredRVPresentation hc S k) {
    toFun := measuredRVSemiringClass hc
    iso := fun h => by obtain ⟨e⟩ := h; exact measuredRVSemiringClass_iso hc e
    empty := measuredRVSemiringClass_empty hc
    scissor := measuredRVSemiringClass_scissor hc }

@[simp] theorem measuredRVKPlusToSemiring_class (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) :
    measuredRVKPlusToSemiring hc (measuredRVClass hc U) = measuredRVSemiringClass hc U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def measuredRVSemiringUniversal (hc : CanonicalStructure.IsCanonical (M := M))
    {R : Type} [CommSemiring R] :
    PositiveGrothendieck.Invariant (measuredRVSemiringPresentation (M := M) hc S) (R := R) ≃
      (MeasuredRVPositiveSemiring hc S →+* R) := PositiveGrothendieck.universalEquiv _

end DiamondIntegral.Section3
