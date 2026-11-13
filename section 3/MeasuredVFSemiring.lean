import «section 3».MeasuredVFProducts
import Section4.PositivePresentation

/-! The measured VF semiring uses the original essential groupoids in
positive degree and genuine form-preserving bijections in degree zero.
The uniform data equivalence only supplies actual object products. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (VFType (M := M))]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))

abbrev GradedMeasuredVFData := Σ k, MeasuredVFData C hc k

def gradedMeasuredVFIso (A B : GradedMeasuredVFData C hc) : Prop :=
  ∃ k, ∃ a b : MeasuredVFData C hc k, Nonempty (a.toObject ≅ b.toObject) ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedMeasuredVFScissor (A B D E : GradedMeasuredVFData C hc) : Prop :=
  (∃ k, ∃ a b d e : MeasuredVFData C hc k,
    (measuredVFPresentation C hc k).scissor a.toObject b.toObject d.toObject e.toObject ∧
      A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, MeasuredVFData.empty C hc k⟩ ∧ B = ⟨0, MeasuredVFData.empty C hc 0⟩ ∧
    D = ⟨0, MeasuredVFData.empty C hc 0⟩ ∧ E = ⟨0, MeasuredVFData.empty C hc 0⟩)

def measuredVFSemiringPresentation : PositiveGrothendieck.Presentation (GradedMeasuredVFData C hc) where
  iso := gradedMeasuredVFIso C hc
  empty := ⟨0, MeasuredVFData.empty C hc 0⟩
  unit := ⟨0, MeasuredVFData.unit C hc⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedMeasuredVFScissor C hc

abbrev MeasuredVFPositiveSemiring := PositiveGrothendieck.KPlus (measuredVFSemiringPresentation C hc)
abbrev MeasuredVFGrothendieckRing := Algebra.GrothendieckAddGroup (MeasuredVFPositiveSemiring C hc)

def measuredVFDataSemiringClass {k : ℕ} (A : MeasuredVFData C hc k) : MeasuredVFPositiveSemiring C hc :=
  PositiveGrothendieck.of (measuredVFSemiringPresentation C hc) ⟨k, A⟩

def measuredVFObjectSemiringClass {k : ℕ} (A : MeasuredVFObject C hc k) : MeasuredVFPositiveSemiring C hc :=
  measuredVFDataSemiringClass C hc (MeasuredVFData.ofObject A)

theorem measuredVFDataSemiringClass_iso {k : ℕ} {A B : MeasuredVFData C hc k}
    (e : A.toObject ≅ B.toObject) :
    measuredVFDataSemiringClass C hc A = measuredVFDataSemiringClass C hc B :=
  PositiveGrothendieck.of_iso (measuredVFSemiringPresentation C hc) ⟨k, A, B, ⟨e⟩, rfl, rfl⟩

@[simp] theorem measuredVFDataSemiringClass_empty {k : ℕ} :
    measuredVFDataSemiringClass C hc (MeasuredVFData.empty C hc k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (measuredVFSemiringPresentation C hc)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (measuredVFSemiringPresentation C hc)
      ⟨0, MeasuredVFData.empty C hc 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem measuredVFObjectSemiringClass_empty {k : ℕ} :
    measuredVFObjectSemiringClass C hc (measuredVFPresentation C hc k).empty = 0 := by
  cases k <;> exact measuredVFDataSemiringClass_empty C hc

theorem measuredVFDataSemiringClass_product {k l : ℕ}
    (A : MeasuredVFData C hc k) (B : MeasuredVFData C hc l) :
    measuredVFDataSemiringClass C hc (A.product B) =
      measuredVFDataSemiringClass C hc A * measuredVFDataSemiringClass C hc B :=
  PositiveGrothendieck.of_product (measuredVFSemiringPresentation C hc) ⟨k, A⟩ ⟨l, B⟩

theorem measuredVFObjectSemiringClass_scissor {k : ℕ}
    {A B D E : MeasuredVFObject C hc k} (h : (measuredVFPresentation C hc k).scissor A B D E) :
    measuredVFObjectSemiringClass C hc A + measuredVFObjectSemiringClass C hc B =
      measuredVFObjectSemiringClass C hc D + measuredVFObjectSemiringClass C hc E := by
  apply PositiveGrothendieck.of_scissor (measuredVFSemiringPresentation C hc)
  exact Or.inl ⟨k, MeasuredVFData.ofObject A, MeasuredVFData.ofObject B,
    MeasuredVFData.ofObject D, MeasuredVFData.ofObject E,
    by simpa only [MeasuredVFData.to_ofObject] using h, rfl, rfl, rfl, rfl⟩

def measuredVFKPlusToSemiring {k : ℕ} : MeasuredVFKPlus C hc k →+ MeasuredVFPositiveSemiring C hc :=
  PositiveAdditiveGrothendieck.lift (measuredVFPresentation C hc k) {
    toFun := measuredVFObjectSemiringClass C hc
    iso := by
      intro A B h
      have he : Nonempty (A ≅ B) := by cases k <;> exact h
      obtain ⟨e⟩ := he
      exact measuredVFDataSemiringClass_iso C hc
        (by simpa only [MeasuredVFData.to_ofObject] using e)
    empty := measuredVFObjectSemiringClass_empty C hc
    scissor := measuredVFObjectSemiringClass_scissor C hc }

@[simp] theorem measuredVFKPlusToSemiring_class {k : ℕ} (A : MeasuredVFObject C hc k) :
    measuredVFKPlusToSemiring C hc (positiveClass (measuredVFPresentation C hc k) A) =
      measuredVFObjectSemiringClass C hc A := PositiveAdditiveGrothendieck.lift_of _ _ A

end DiamondIntegral.Section3
