import «section 4».Section3LinkedRetractionStatements
import «section 4».RVT001NormalizedDistinct
import «section 4».RVT001OrdinaryRanges
import «section 5».GammaQEFiniteLaws

/-! The ordinary retraction statements of Remarks 4.4 (`eb:no:eg`) and 4.16
(`eb:not:eg`) and the diagram (edb:eb:com), linked to the finalized Section 3 kernel proofs
(`Section3T001Integration.ordinary`) and with the unary Γ rational-affine
input discharged (`Section5.GammaQE.gamma_piecewise_rational_affine`).
They take no T001 presentation and no Γ-linearity input. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.Section4LinkedRemarks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

/-- The bounded retraction `Ẽ_b` on the normalized ordinary ring. -/
abbrev boundedRetraction :=
  RVT001OrdinaryNormalization.bounded h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
    hκ hs B hr hγ hΓ (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)

/-- The geometric retraction `Ẽ_g` on the normalized ordinary ring. -/
abbrev geometricRetraction :=
  RVT001OrdinaryNormalization.geometric h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
    hκ hs B hr hγ hΓ (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)

/-- The diagram (edb:eb:com): `Ẽ_b` after forgetting volume forms equals the
bounded radius evaluation followed by the dimension-free identification. -/
theorem diagram_edb_eb_com :
    (boundedRetraction hc h00 hκ hs B hr hγ hΓ).comp (RVOrdinaryPNormalization.forget B) =
      (RESDimensionFreeReduction.fromGradedReduced B).comp
        (RVT001OrdinaryDescent.radiusEvaluation h00
          (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
          (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) EulerKind.bounded) :=
  RVT001OrdinaryNormalization.bounded_radius_square h00 _ hκ hs B hr hγ hΓ _

/-- `Ẽ_b` restricts to the dimension-free identification on RES classes. -/
theorem boundedRetraction_res (x : RESOrdinaryRing.Ring B) :
    boundedRetraction hc h00 hκ hs B hr hγ hΓ (RVOrdinaryPNormalization.ofRES B x) =
      RESDimensionFreeReduction.fromOrdinary B x :=
  RVT001OrdinaryNormalization.bounded_res h00 _ hκ hs B hr hγ hΓ _ x

/-- `Ẽ_b` is surjective. -/
theorem boundedRetraction_surjective :
    Function.Surjective (boundedRetraction hc h00 hκ hs B hr hγ hΓ) :=
  RVT001OrdinaryRanges.bounded_surjective h00 _ hκ hs B hr hγ hΓ _

/-- The range of `Ẽ_g` is the range of the affine comparison. -/
theorem geometricRetraction_range :
    Set.range (geometricRetraction hc h00 hκ hs B hr hγ hΓ) =
      Set.range (RESAffineLocalization.comparison B) :=
  RVT001OrdinaryRanges.geometric_range h00 _ hκ hs B hr hγ hΓ _

/-- Remarks 4.4 and 4.16 (`eb:no:eg`, `eb:not:eg`): after normalization the geometric and
bounded retractions differ (the point class goes to `[A]⁻¹` and to `1`). -/
theorem normalized_retractions_distinct :
    geometricRetraction hc h00 hκ hs B hr hγ hΓ ≠
      RVT001NormalizedDistinct.boundedInAffine h00
        (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
        (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) :=
  RVT001NormalizedDistinct.normalized_maps_distinct hc h00 _ hκ hs B hr hγ hΓ _

end DiamondIntegral.Section4.Section4LinkedRemarks
