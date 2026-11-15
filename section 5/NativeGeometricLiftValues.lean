import «section 5».NativeVFPullbackValues

/-! The actual geometric VF value of a positive lift is its raw numerator
normalized in the lift degree. Actual affine RV padding changes neither
that VF value nor the fibre equality criterion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

theorem nativeVFGeometricValue_lift_fraction (A : GammaGroundFiniteVFObject hc G.base)
    {k : ℕ} (U : GammaGroundRVObject hc G.base k) (e : GammaGroundBijection A.domain (gammaGroundObjectLift U)) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine G.base)
        (nativeGroundRVEvaluation G.model00 linear G.uncountable.le G.saturated hc G.base
          G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric (ordinaryClass U)) k :=
  (nativeVFGeometricValue_of_lift_bijection linear H A U e).trans
    (nativeGroundGeometricRetraction_class G.model00 linear G.uncountable.le G.saturated
      G.small_real G.small_gamma G.nontrivial_definable_gamma U)

theorem nativeVFGeometricValue_equal_iff_padded_lifts (A D : GammaGroundFiniteVFObject hc G.base)
    {k l : ℕ} (U : GammaGroundRVObject hc G.base k) (V : GammaGroundRVObject hc G.base l)
    (e : GammaGroundBijection A.domain (gammaGroundObjectLift U))
    (f : GammaGroundBijection D.domain (gammaGroundObjectLift V)) :
    nativeVFGeometricValue linear H (nativeVFClass A) = nativeVFGeometricValue linear H (nativeVFClass D) ↔
      ∃ N : ℕ,k ≤ N ∧ l ≤ N ∧
        nativeGroundRVEvaluation G.model00 linear G.uncountable.le G.saturated hc G.base
          G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric
          (ordinaryClass (U.product (nativeAffineRVPower hc G.base (N-k)))) =
        nativeGroundRVEvaluation G.model00 linear G.uncountable.le G.saturated hc G.base
          G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric
          (ordinaryClass (V.product (nativeAffineRVPower hc G.base (N-l)))) := by
  rw [nativeVFGeometricValue_of_lift_bijection linear H A U e,
    nativeVFGeometricValue_of_lift_bijection linear H D V f]
  exact nativeGroundGeometricRetraction_eq_iff_common_degree G.model00 linear G.uncountable.le G.saturated
    G.small_real G.small_gamma G.nontrivial_definable_gamma U V

theorem nativeVFGeometricValue_nonzero_pullback (A : GammaGroundFiniteVFObject hc G.base)
    (hpull : IsRVPullback A.domain.carrier) (hnz : ∀ a : A.domain,∀ i : Fin A.vfArity,a.val.1 i ≠ 0) :
    nativeVFGeometricValue linear H (nativeVFClass A) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine G.base)
        (nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
          G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric (nativeMixedFullKeyMap A.domain).image)
        A.vfArity := by
  let U := nativePullbackRVObject G.uncountable.le G.saturated G.model00 G.small_real A.domain hpull A.finite hnz
  have he := nativeVFGeometricValue_lift_fraction linear H A U
    (nativePullbackRVObject_lift_bijection G.uncountable.le G.saturated G.model00 G.small_real A.domain hpull A.finite hnz)
  exact he.trans (congrArg (fun a => geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine G.base) a A.vfArity)
    (nativeRVSetValue_object G.model00 linear G.uncountable.le G.saturated hc G.base
      G.small_real G.small_gamma G.nontrivial_definable_gamma .geometric U).symm)

end DiamondIntegral.Section5
