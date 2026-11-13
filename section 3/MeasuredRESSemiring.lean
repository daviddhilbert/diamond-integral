import «section 3».MeasuredRVProducts
import «section 3».RESScissors
import Section4.PositivePresentation

/-! The measured RES semiring uses full finite source-value support,
actual product forms and the pointwise Gamma-preserving arrows. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def MeasuredRESObject.product (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k) (V : MeasuredRESObject (M := M) S l) :
    MeasuredRESObject S (k + l) :=
  ⟨U.obj.product hc V.obj, RVObject.product_res U.property V.property⟩

def MeasuredRESObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    MeasuredRESObject (M := M) S 0 :=
  ⟨MeasuredRVObject.unit hc S, (RVObject.unit S).degree_zero_res⟩

abbrev GradedMeasuredRESObject (S : Set M) := Σ k, MeasuredRESObject (M := M) S k

def gradedMeasuredRESIso (A B : GradedMeasuredRESObject (M := M) S) : Prop :=
  ∃ k, ∃ a b : MeasuredRESObject S k, Nonempty (a ≅ b) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedMeasuredRESScissor (hc : CanonicalStructure.IsCanonical (M := M))
    (A B D E : GradedMeasuredRESObject (M := M) S) : Prop :=
  (∃ k, ∃ a b d e : MeasuredRESObject S k,
    MeasuredRVScissor hc a.obj b.obj d.obj e.obj ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, MeasuredRESObject.empty S k⟩ ∧ B = ⟨0, MeasuredRESObject.empty S 0⟩ ∧
    D = ⟨0, MeasuredRESObject.empty S 0⟩ ∧ E = ⟨0, MeasuredRESObject.empty S 0⟩)

def measuredRESSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    PositiveGrothendieck.Presentation (GradedMeasuredRESObject (M := M) S) where
  iso := gradedMeasuredRESIso
  empty := ⟨0, MeasuredRESObject.empty S 0⟩
  unit := ⟨0, MeasuredRESObject.unit hc S⟩
  product A B := ⟨A.1 + B.1, A.2.product hc B.2⟩
  scissor := gradedMeasuredRESScissor hc

abbrev MeasuredRESPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  PositiveGrothendieck.KPlus (measuredRESSemiringPresentation (M := M) hc S)
abbrev MeasuredRESGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :=
  Algebra.GrothendieckAddGroup (MeasuredRESPositiveSemiring (M := M) hc S)

def measuredRESSemiringClass (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k) : MeasuredRESPositiveSemiring hc S :=
  PositiveGrothendieck.of (measuredRESSemiringPresentation hc S) ⟨k, U⟩

theorem measuredRESSemiringClass_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRESObject (M := M) S k} (e : U ≅ V) :
    measuredRESSemiringClass hc U = measuredRESSemiringClass hc V :=
  PositiveGrothendieck.of_iso (measuredRESSemiringPresentation hc S) ⟨k, U, V, ⟨e⟩, rfl, rfl⟩

@[simp] theorem measuredRESSemiringClass_empty (hc : CanonicalStructure.IsCanonical (M := M)) :
    measuredRESSemiringClass hc (MeasuredRESObject.empty (M := M) S k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (measuredRESSemiringPresentation (M := M) hc S)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (measuredRESSemiringPresentation (M := M) hc S)
      ⟨0, MeasuredRESObject.empty S 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem measuredRESSemiringClass_unit (hc : CanonicalStructure.IsCanonical (M := M)) :
    measuredRESSemiringClass hc (MeasuredRESObject.unit (M := M) hc S) = 1 :=
  PositiveGrothendieck.of_unit (measuredRESSemiringPresentation hc S)

theorem measuredRESSemiringClass_product (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k) (V : MeasuredRESObject (M := M) S l) :
    measuredRESSemiringClass hc (U.product hc V) =
      measuredRESSemiringClass hc U * measuredRESSemiringClass hc V :=
  PositiveGrothendieck.of_product (measuredRESSemiringPresentation hc S) ⟨k, U⟩ ⟨l, V⟩

theorem measuredRESSemiringClass_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    {A B D E : MeasuredRESObject (M := M) S k} (h : MeasuredRVScissor hc A.obj B.obj D.obj E.obj) :
    measuredRESSemiringClass hc A + measuredRESSemiringClass hc B =
      measuredRESSemiringClass hc D + measuredRESSemiringClass hc E :=
  PositiveGrothendieck.of_scissor (measuredRESSemiringPresentation hc S)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def measuredRESKPlusToSemiring (hc : CanonicalStructure.IsCanonical (M := M)) :
    MeasuredRESKPlus hc S k →+ MeasuredRESPositiveSemiring hc S :=
  PositiveAdditiveGrothendieck.lift (measuredRESPresentation hc S k) {
    toFun := measuredRESSemiringClass hc
    iso := fun h => by obtain ⟨e⟩ := h; exact measuredRESSemiringClass_iso hc e
    empty := measuredRESSemiringClass_empty hc
    scissor := measuredRESSemiringClass_scissor hc }

@[simp] theorem measuredRESKPlusToSemiring_class (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRESObject (M := M) S k) :
    measuredRESKPlusToSemiring hc (measuredResClass hc U) = measuredRESSemiringClass hc U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def measuredRESSemiringUniversal (hc : CanonicalStructure.IsCanonical (M := M))
    {R : Type} [CommSemiring R] :
    PositiveGrothendieck.Invariant (measuredRESSemiringPresentation (M := M) hc S) (R := R) ≃
      (MeasuredRESPositiveSemiring hc S →+* R) := PositiveGrothendieck.universalEquiv _

end DiamondIntegral.Section3
