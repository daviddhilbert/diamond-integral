import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowMeasuredContinuousCoordinateRootStep

/-! (Row-form version for Remark 6.20, translated from `ExactGammaTransport`.)
 Exact pointwise form transportRow along a special bijection identifies
the target form with inverse composition. Its levels inherit the checked
proper geometry without an extra target-level hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem exact_gamma_transport_eq_inverse_row (f : Map A B) (hf : Function.Bijective f)
    (ω : RowFormOn A qR)
    (η : RowFormOn B qR)
    (hTransport : ∀ p : A, (η (f p)).val = (ω p).val) : η = ω.comp (f.inverse hf) := by
  apply RowFormOn.ext
  intro q
  have h := hTransport (f.inverse hf q)
  rw [Map.apply_inverse] at h
  exact Subtype.ext h

theorem SpecialCovariantChain.exact_gamma_levels_open_row {f : Map A B}
    (h : SpecialCovariantChain (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ})
    (η : RowFormOn B qR)
    (hTransport : ∀ p : A, (η (f p)).val = (ω p).val) :
    ∀ u γ, IsOpen {b : Fin n → VF M | (b,u) ∈ B.carrier ∧ rowFormExtension η (b,u) = γ} := by
  have he := exact_gamma_transport_eq_inverse_row f (h.bijective h00) ω η hTransport
  rw [he]
  have hGeometry := h.gamma_levels_proper_geometry_row h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  exact fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen

end DiamondIntegral.Section6
