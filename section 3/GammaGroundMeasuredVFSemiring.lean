import «section 3».GammaGroundContext
import «section 3».GammaGroundMeasuredVFScissors
import «section 3».GammaGroundMeasuredVFProducts
import Section4.PositivePresentation

/-! Universal cartesian measured VF presentation over the complete
Gamma ground. The actual graded additive comparison is separate. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

abbrev GradedGammaGroundMeasuredVFData := Σ k, GammaGroundMeasuredVFData hc C.base k

def gradedGammaGroundMeasuredVFIso (A B : GradedGammaGroundMeasuredVFData C hc) : Prop :=
  ∃ k, ∃ a b : GammaGroundMeasuredVFData hc C.base k,
    Nonempty (GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small_real hv a b) ∧
      A = ⟨k, a⟩ ∧ B = ⟨k, b⟩

def gradedGammaGroundMeasuredVFScissor (A B D E : GradedGammaGroundMeasuredVFData C hc) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundMeasuredVFData hc C.base k,
    gammaGroundMeasuredVFScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundMeasuredVFData.empty hc C.base k⟩ ∧ B = ⟨0, GammaGroundMeasuredVFData.empty hc C.base 0⟩ ∧
    D = ⟨0, GammaGroundMeasuredVFData.empty hc C.base 0⟩ ∧ E = ⟨0, GammaGroundMeasuredVFData.empty hc C.base 0⟩)

def gammaGroundMeasuredVFSemiringPresentation : PositiveGrothendieck.Presentation (GradedGammaGroundMeasuredVFData C hc) where
  iso := gradedGammaGroundMeasuredVFIso C hc hv
  empty := ⟨0, GammaGroundMeasuredVFData.empty hc C.base 0⟩
  unit := ⟨0, GammaGroundMeasuredVFData.unit hc C.base⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedGammaGroundMeasuredVFScissor C hc

abbrev GammaGroundMeasuredVFPositiveSemiring := PositiveGrothendieck.KPlus (gammaGroundMeasuredVFSemiringPresentation C hc hv)
abbrev GammaGroundMeasuredVFGrothendieckRing := Algebra.GrothendieckAddGroup (GammaGroundMeasuredVFPositiveSemiring C hc hv)

def gammaGroundMeasuredVFSemiringClass {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    GammaGroundMeasuredVFPositiveSemiring C hc hv := PositiveGrothendieck.of (gammaGroundMeasuredVFSemiringPresentation C hc hv) ⟨k, U⟩

theorem gammaGroundMeasuredVFSemiringClass_iso {k : ℕ} {U V : GammaGroundMeasuredVFData hc C.base k}
    (f : GammaGroundMeasuredVFHom C.uncountable.le C.saturated C.small_real hv U V) :
    gammaGroundMeasuredVFSemiringClass C hc hv U = gammaGroundMeasuredVFSemiringClass C hc hv V :=
  PositiveGrothendieck.of_iso (gammaGroundMeasuredVFSemiringPresentation C hc hv) ⟨k, U, V, ⟨f⟩, rfl, rfl⟩

@[simp] theorem gammaGroundMeasuredVFSemiringClass_empty {k : ℕ} :
    gammaGroundMeasuredVFSemiringClass C hc hv (GammaGroundMeasuredVFData.empty hc C.base k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundMeasuredVFSemiringPresentation C hc hv)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundMeasuredVFSemiringPresentation C hc hv)
      ⟨0, GammaGroundMeasuredVFData.empty hc C.base 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundMeasuredVFSemiringClass_unit :
    gammaGroundMeasuredVFSemiringClass C hc hv (GammaGroundMeasuredVFData.unit hc C.base) = 1 := PositiveGrothendieck.of_unit _

theorem gammaGroundMeasuredVFSemiringClass_product {k l : ℕ}
    (U : GammaGroundMeasuredVFData hc C.base k) (V : GammaGroundMeasuredVFData hc C.base l) :
    gammaGroundMeasuredVFSemiringClass C hc hv (U.product V) =
      gammaGroundMeasuredVFSemiringClass C hc hv U * gammaGroundMeasuredVFSemiringClass C hc hv V :=
  PositiveGrothendieck.of_product (gammaGroundMeasuredVFSemiringPresentation C hc hv) ⟨k, U⟩ ⟨l, V⟩

theorem gammaGroundMeasuredVFSemiringClass_scissor {k : ℕ} {A B D E : GammaGroundMeasuredVFData hc C.base k}
    (h : gammaGroundMeasuredVFScissor A B D E) :
    gammaGroundMeasuredVFSemiringClass C hc hv A + gammaGroundMeasuredVFSemiringClass C hc hv B =
      gammaGroundMeasuredVFSemiringClass C hc hv D + gammaGroundMeasuredVFSemiringClass C hc hv E :=
  PositiveGrothendieck.of_scissor (gammaGroundMeasuredVFSemiringPresentation C hc hv)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundMeasuredVFKPlusToSemiring {k : ℕ} :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k →+
      GammaGroundMeasuredVFPositiveSemiring C hc hv :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredVFPresentation (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) {
    toFun := gammaGroundMeasuredVFSemiringClass C hc hv
    iso := fun h => by obtain ⟨f⟩ := h; exact gammaGroundMeasuredVFSemiringClass_iso C hc hv f
    empty := gammaGroundMeasuredVFSemiringClass_empty C hc hv
    scissor := gammaGroundMeasuredVFSemiringClass_scissor C hc hv }

@[simp] theorem gammaGroundMeasuredVFKPlusToSemiring_class {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    gammaGroundMeasuredVFKPlusToSemiring C hc hv (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv U) =
      gammaGroundMeasuredVFSemiringClass C hc hv U := PositiveAdditiveGrothendieck.lift_of _ _ U

end DiamondIntegral.Section3
