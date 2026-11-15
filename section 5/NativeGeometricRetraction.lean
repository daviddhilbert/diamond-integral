import «section 5».NativeBoundedRetraction
import «section 5».GeometricDegreeClearing
import «section 4».RVT001OrdinaryNormalization

/-! The actual geometric retraction retains degree normalization in the
affine-localized target and factors through the VF lifting relation. The
geometric raw Euler map with degree forgotten is its numerator only. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def nativeGeometricRetraction : RVOrdinaryPNormalization.Ring B →+* RESAffineLocalization.Target B :=
  RVT001OrdinaryNormalization.geometric h00 linear hκ hs B hr hγ hΓ
    (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ)

theorem nativeGeometricRetraction_class {k : ℕ} (U : RVMeasuredCharts.Chart B k) :
    nativeGeometricRetraction h00 linear hκ hs hc B hr hγ hΓ
      (RVOrdinaryPNormalization.quotient B (RVOrdinaryRing.objectClass U)) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
        (nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ EulerKind.geometric
          (RVOrdinaryRing.objectClass U)) k := by
  let P := Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ
  let x := RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ P EulerKind.geometric
    (RVOrdinaryRing.objectClass U)
  have hx : x ∈ RESReductionGradings.ordinaryPiece B k :=
    (RVT001OrdinaryDescent.gradedEvaluation h00 linear hκ hs B hr hγ hΓ P EulerKind.geometric).map_mem
      (RVOrdinaryGrading.class_mem B U)
  change RESAffineLocalization.comparison B (RESAffineNormalization.normalize B x) = _
  have he := RESAffineNormalization.comparison_homogeneous B hx
  exact he.trans (Localization.mk_eq_mk'_apply _ _)

theorem nativeGeometricRetraction_point :
    nativeGeometricRetraction h00 linear hκ hs hc B hr hγ hΓ
      (RVOrdinaryPNormalization.quotient B (RVOrdinaryRing.objectClass (RESPointTuples.chart B 1))) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B) 1 1 := by
  rw [nativeGeometricRetraction_class,nativeRVEvaluation_point]

theorem nativeGeometricRetraction_equal_degree_clearing {k l : ℕ}
    (U : RVMeasuredCharts.Chart B k) (V : RVMeasuredCharts.Chart B l) :
    nativeGeometricRetraction h00 linear hκ hs hc B hr hγ hΓ
      (RVOrdinaryPNormalization.quotient B (RVOrdinaryRing.objectClass U)) =
    nativeGeometricRetraction h00 linear hκ hs hc B hr hγ hΓ
      (RVOrdinaryPNormalization.quotient B (RVOrdinaryRing.objectClass V)) ↔
      ∃ N : ℕ, k ≤ N ∧ l ≤ N ∧
        RESAffineLocalization.dimensionFreeAffine B ^ (N-k) *
          nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ EulerKind.geometric
            (RVOrdinaryRing.objectClass U) =
        RESAffineLocalization.dimensionFreeAffine B ^ (N-l) *
          nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ EulerKind.geometric
            (RVOrdinaryRing.objectClass V) := by
  rw [nativeGeometricRetraction_class,nativeGeometricRetraction_class,geometricDegreeValue_eq_iff]

end DiamondIntegral.Section5
