import «section 4».Section3LinkedRetractionStatements
import «section 4».RVT001NormalizedDistinct
import «section 4».RVT001OrdinaryRanges
import «section 4».RelativeAnnularGenerators
import «section 5».GammaQEFiniteLaws
import «section 4».RVT001AlternativeDescent

/-! The ordinary retraction statements of Remarks 4.4 (`eb:no:eg`) and 4.16
(`eb:not:eg`) and the diagram (edb:eb:com), linked to the finalized Section 3 kernel proofs
(`Section3T001Integration.ordinary`) and with the unary Γ rational-affine
input discharged (`Section5.GammaQE.gamma_piecewise_rational_affine`).
They take no T001 presentation and no Γ-linearity input. The same is done
for Remark 4.8's alternative descent (measured kernel,
`Section3T001Integration.measured`) and for the unnormalized ordinary range
clauses. -/

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

/-- Lemma 4.18 (factorization clause) with the Γ input discharged: the bounded
retraction kills the manuscript ideal, so it factors through `B / J_var`. -/
theorem manuscript_section4_compatibility_discharged :
    RelativeAnnularGenerators.manuscriptIdeal B ≤ RingHom.ker
      (RVT001OrdinaryDescent.boundedEvaluation h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
        hκ hs B hr hγ hΓ (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) EulerKind.bounded) :=
  RelativeAnnularGenerators.manuscript_section4_compatibility hc h00 _ hκ hs B hr hγ hΓ

/-! ### Remark 4.8 (`res:forget`): the alternative descent, linked -/

/-- Remark 4.8's alternative geometric descent `μRV[*] → K(RES)/(alternative)`,
with the finalized Section 3 measured kernel and the discharged Γ input. -/
abbrev alternativeEvaluation : RVChartRing.Ring B →+* RESAlternativeReduction.Ring B :=
  RVT001AlternativeDescent.evaluation h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
    hκ hs B hr hγ hΓ (Section3T001Integration.measured (hc := hc) hκ hs h00 hr hγ hΓ)

/-- The graded form of `alternativeEvaluation`. -/
abbrev alternativeGradedEvaluation :=
  RVT001AlternativeDescent.gradedEvaluation h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
    hκ hs B hr hγ hΓ (Section3T001Integration.measured (hc := hc) hκ hs h00 hr hγ hΓ)

/-- On RES classes the alternative descent is the forgetful map. -/
theorem alternativeEvaluation_res (x : RESChartRing.Ring B) :
    alternativeEvaluation hc h00 hκ hs B hr hγ hΓ (RVChartMaps.ofRES B x) =
      RESAlternativeReduction.fromMeasured B x :=
  RVT001AlternativeDescent.evaluation_res h00 _ hκ hs B hr hγ hΓ _ x

theorem alternativeEvaluation_p :
    alternativeEvaluation hc h00 hκ hs B hr hγ hΓ (RVMeasuredSpecialClasses.pClass B) = 0 :=
  RVT001AlternativeDescent.evaluation_p h00 _ hκ hs B hr hγ hΓ _

theorem alternativeEvaluation_h :
    alternativeEvaluation hc h00 hκ hs B hr hγ hΓ (RVMeasuredSpecialClasses.hClass B) =
      RESAlternativeReduction.pointClass B :=
  RVT001AlternativeDescent.evaluation_h h00 _ hκ hs B hr hγ hΓ _

/-! ### Unnormalized ordinary range clauses, linked -/

/-- The ordinary Euler evaluations after T001 descent are onto the reduced RES ring. -/
theorem ordinaryEvaluation_surjective (kind : EulerKind) :
    Function.Surjective (RVT001OrdinaryDescent.evaluation h00
      (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) kind) :=
  RVT001OrdinaryRanges.evaluation_surjective h00 _ hκ hs B hr hγ hΓ _ kind

theorem ordinaryBoundedEvaluation_surjective (kind : EulerKind) :
    Function.Surjective (RVT001OrdinaryDescent.boundedEvaluation h00
      (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) kind) :=
  RVT001OrdinaryRanges.boundedEvaluation_surjective h00 _ hκ hs B hr hγ hΓ _ kind

theorem ordinaryRadiusEvaluation_surjective (kind : EulerKind) :
    Function.Surjective (RVT001OrdinaryDescent.radiusEvaluation h00
      (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) kind) :=
  RVT001OrdinaryRanges.radiusEvaluation_surjective h00 _ hκ hs B hr hγ hΓ _ kind

theorem boundedRaw_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.boundedRaw h00
      (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)) :=
  RVT001OrdinaryRanges.boundedRaw_surjective h00 _ hκ hs B hr hγ hΓ _

theorem homogeneousRaw_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.homogeneousRaw h00
      (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)) :=
  RVT001OrdinaryRanges.homogeneousRaw_surjective h00 _ hκ hs B hr hγ hΓ _

theorem homogeneousRetraction_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.homogeneous h00
      (Section5.GammaQE.gamma_piecewise_rational_affine (M := M)) hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)) :=
  RVT001OrdinaryRanges.homogeneous_surjective h00 _ hκ hs B hr hγ hΓ _

end DiamondIntegral.Section4.Section4LinkedRemarks
