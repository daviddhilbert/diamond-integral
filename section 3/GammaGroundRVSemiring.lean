import «section 3».GammaGroundRVProducts
import Section4.PositivePresentation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

abbrev GradedGammaGroundRVObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := Σ k, GammaGroundRVObject (M := M) hc ground k

def gradedGammaGroundRVScissor (A B D E : GradedGammaGroundRVObject (M := M) hc ground) : Prop :=
  (∃ k, ∃ a b d e : GammaGroundRVObject hc ground k,
    gammaGroundRVScissor a b d e ∧ A = ⟨k, a⟩ ∧ B = ⟨k, b⟩ ∧ D = ⟨k, d⟩ ∧ E = ⟨k, e⟩) ∨
  (∃ k, A = ⟨k, GammaGroundRVObject.empty hc ground k⟩ ∧ B = ⟨0, GammaGroundRVObject.empty hc ground 0⟩ ∧
    D = ⟨0, GammaGroundRVObject.empty hc ground 0⟩ ∧ E = ⟨0, GammaGroundRVObject.empty hc ground 0⟩)

def gammaGroundRVSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) :
    PositiveGrothendieck.Presentation (GradedGammaGroundRVObject (M := M) hc ground) where
  iso A B := A.1 = B.1 ∧ Nonempty (GammaGroundBijection A.2.domain B.2.domain)
  empty := ⟨0, GammaGroundRVObject.empty hc ground 0⟩
  unit := ⟨0, GammaGroundRVObject.unit hc ground⟩
  product A B := ⟨A.1 + B.1, A.2.product B.2⟩
  scissor := gradedGammaGroundRVScissor

abbrev GammaGroundRVPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := PositiveGrothendieck.KPlus (gammaGroundRVSemiringPresentation (M := M) hc ground)
abbrev GammaGroundRVGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) := Algebra.GrothendieckAddGroup (GammaGroundRVPositiveSemiring (M := M) hc ground)

def gammaGroundRVSemiringClass (U : GammaGroundRVObject (M := M) hc ground k) : GammaGroundRVPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundRVSemiringPresentation hc ground) ⟨k, U⟩

theorem gammaGroundRVSemiringClass_iso {U V : GammaGroundRVObject (M := M) hc ground k} (e : U ≅ V) :
    gammaGroundRVSemiringClass U = gammaGroundRVSemiringClass V :=
  PositiveGrothendieck.of_iso (gammaGroundRVSemiringPresentation hc ground) ⟨rfl, ⟨e.hom⟩⟩

@[simp] theorem gammaGroundRVSemiringClass_empty : gammaGroundRVSemiringClass (GammaGroundRVObject.empty (M := M) hc ground k) = 0 := by
  have h := PositiveGrothendieck.of_scissor (gammaGroundRVSemiringPresentation (M := M) hc ground)
    (Or.inr ⟨k, rfl, rfl, rfl, rfl⟩)
  have he : PositiveGrothendieck.of (gammaGroundRVSemiringPresentation (M := M) hc ground)
      ⟨0, GammaGroundRVObject.empty hc ground 0⟩ = 0 := PositiveGrothendieck.of_empty _
  rw [he, add_zero, add_zero] at h
  exact h

@[simp] theorem gammaGroundRVSemiringClass_unit : gammaGroundRVSemiringClass (GammaGroundRVObject.unit (M := M) hc ground) = 1 :=
  PositiveGrothendieck.of_unit (gammaGroundRVSemiringPresentation hc ground)

theorem gammaGroundRVSemiringClass_product (U : GammaGroundRVObject (M := M) hc ground k) (V : GammaGroundRVObject (M := M) hc ground l) :
    gammaGroundRVSemiringClass (U.product V) = gammaGroundRVSemiringClass U * gammaGroundRVSemiringClass V :=
  PositiveGrothendieck.of_product (gammaGroundRVSemiringPresentation hc ground) ⟨k, U⟩ ⟨l, V⟩

theorem gammaGroundRVSemiringClass_scissor {A B D E : GammaGroundRVObject (M := M) hc ground k} (h : gammaGroundRVScissor A B D E) :
    gammaGroundRVSemiringClass A + gammaGroundRVSemiringClass B = gammaGroundRVSemiringClass D + gammaGroundRVSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundRVSemiringPresentation hc ground)
    (Or.inl ⟨k, A, B, D, E, h, rfl, rfl, rfl, rfl⟩)

def gammaGroundRVKPlusToSemiring : GammaGroundRVKPlus (M := M) hc ground k →+ GammaGroundRVPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundRVPresentation hc ground k) {
    toFun := gammaGroundRVSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundRVSemiringClass_iso e
    empty := gammaGroundRVSemiringClass_empty
    scissor := gammaGroundRVSemiringClass_scissor }

@[simp] theorem gammaGroundRVKPlusToSemiring_class (U : GammaGroundRVObject (M := M) hc ground k) :
    gammaGroundRVKPlusToSemiring (gammaGroundRVClass U) = gammaGroundRVSemiringClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def gammaGroundRVSemiringUniversal {R : Type} [CommSemiring R] :
    PositiveGrothendieck.Invariant (gammaGroundRVSemiringPresentation (M := M) hc ground) (R := R) ≃
      (GammaGroundRVPositiveSemiring hc ground →+* R) := PositiveGrothendieck.universalEquiv _


end DiamondIntegral.Section3
