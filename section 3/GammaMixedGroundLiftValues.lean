import «section 3».GammaMixedNativeLiftValues
import «section 3».GammaMixedFullBijectionValues
import «section 3».GammaGroundUnaryOriginalBaseKernel

/-! The contraction detector recovers the principal class on the
actual ground lift by the checked native round trips in every positive
degree. No unary restriction is used in these round-trip maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMixed_ground_lift_value
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : GammaGroundMeasuredRVObject hc B (n+1)) :
    gammaMixedContractionValue C hBC hv hNames hGenerated (gammaGroundMeasuredObjectLift U) =
      gammaMeasuredPrincipalValue U := by
  have hBridge := gammaMixed_full_bijection_values C hBC hv hg hNames hGenerated δ hδ hδ1
    (gammaGroundNativeFullMeasuredLiftBridge C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv U)
  exact hBridge.symm.trans ((gammaMixed_native_lift_value C hBC hv hg hNames hGenerated δ hδ hδ1
    (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U)).trans
      (gammaMeasuredPrincipalValue_iso (gammaGroundNativeNormalizationHom U)).symm)

end DiamondIntegral.Section3
