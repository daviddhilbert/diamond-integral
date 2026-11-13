import «section 3».GammaGroundMeasuredRVCategories
import «section 3».GammaGroundRVScissors
import «section 3».GammaGroundVolumeForms

/-! Fixed-degree pointwise measured RV scissors over the entire Gamma
ground. Every cut keeps the original form, including in degree zero. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundMeasuredRVObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundMeasuredRVObject hc ground k :=
  ⟨GammaGroundRVObject.empty hc ground k, gammaGroundOneForm _⟩

def GammaGroundMeasuredRVObject.restrict (U : GammaGroundMeasuredRVObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) : GammaGroundMeasuredRVObject hc ground k :=
  ⟨U.underlying.restrict X hX, U.form.comp (GammaGroundMap.inclusion hX)⟩

def gammaGroundMeasuredRVScissor (A B D E : GammaGroundMeasuredRVObject hc ground k) : Prop :=
  ∃ U : GammaGroundMeasuredRVObject hc ground k,
    ∃ X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.underlying.arity),
    ∃ hX : X.carrier ⊆ U.underlying.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = GammaGroundMeasuredRVObject.empty hc ground k

def gammaGroundMeasuredRVPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : ScissorPresentation (GammaGroundMeasuredRVObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundMeasuredRVObject.empty hc ground k
  scissor := gammaGroundMeasuredRVScissor

abbrev GammaGroundMeasuredRVKPlus (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) := KPlus (gammaGroundMeasuredRVPresentation hc ground k)

def gammaGroundMeasuredRVClass (U : GammaGroundMeasuredRVObject hc ground k) : GammaGroundMeasuredRVKPlus hc ground k :=
  positiveClass (gammaGroundMeasuredRVPresentation hc ground k) U

@[simp] theorem gammaGroundMeasuredRVClass_empty : gammaGroundMeasuredRVClass (GammaGroundMeasuredRVObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundMeasuredRVPresentation hc ground k)

theorem gammaGroundMeasuredRVClass_iso {U V : GammaGroundMeasuredRVObject hc ground k} (e : U ≅ V) :
    gammaGroundMeasuredRVClass U = gammaGroundMeasuredRVClass V := positiveClass_iso (gammaGroundMeasuredRVPresentation hc ground k) ⟨e⟩

theorem gammaGroundMeasuredRVClass_scissor (U : GammaGroundMeasuredRVObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.underlying.arity))
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    gammaGroundMeasuredRVClass (U.restrict X hX) +
      gammaGroundMeasuredRVClass (U.restrict (U.underlying.domain.sdiff X) (fun _ h => h.1)) = gammaGroundMeasuredRVClass U := by
  have h := positiveClass_scissor (gammaGroundMeasuredRVPresentation hc ground k) ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  change gammaGroundMeasuredRVClass _ + gammaGroundMeasuredRVClass _ = gammaGroundMeasuredRVClass _ + gammaGroundMeasuredRVClass _ at h
  simpa only [gammaGroundMeasuredRVClass_empty, add_zero] using h

end DiamondIntegral.Section3
