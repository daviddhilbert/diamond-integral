import «section 3».GammaUnaryOriginalBaseKernel
import «section 3».GammaMeasuredNativeRoundTrips
import «section 3».GammaFullMeasuredFixedMaps

/-! Unary geometric comparison for the actual Gamma-ground RV category,
with the full measured lift and the original parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaGroundNativeFullMeasuredLiftBridge
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredRVObject hc B k) :
    GammaFullMeasuredBijection
      (gammaNativeMeasuredLift (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U))
      (gammaGroundMeasuredObjectLift U) := by
  let e : GammaGroundBijection
      (gammaNativeMeasuredLift (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U)).domain
      (gammaGroundMeasuredObjectLift U).domain :=
    GammaGroundBijection.ofCarrierEq (Section5.groundRVAt_lift_domain U.underlying)
  apply gammaFullMeasuredFixedVF hκ hs hr hv e (fun _ => rfl)
  intro p
  change (gammaGroundFormValue U.form
    ((Section5.groundRVObjectRoundTrip U.underlying).map
      (gammaNativeLiftLabel (Section5.groundRVAt U.underlying) p))).val =
    (gammaGroundFormValue U.form (gammaGroundObjectLiftLabel U.underlying (e.map p))).val
  congr 2

def gammaGroundNativeNormalizationHom (U : GammaGroundMeasuredRVObject hc B (k+1)) :
    GammaGroundMeasuredRVHom U
      (gammaNativeMeasuredNormalization (Section5.groundRVAt U.underlying) (gammaGroundMeasuredNativeForm U)) :=
  (gammaNativeFullWeightNormalizationHom _ (Section5.groundRVAt_full U.underlying)
    (gammaGroundMeasuredNativeForm U)).comp (gammaGroundMeasuredNativeRoundTrip U).symm

theorem gammaGroundUnaryFullMeasured_original_base_geometry
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaGroundMeasuredRVObject hc B 1)
    (f : GammaFullMeasuredBijection (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V)) :
    GammaUnaryMeasuredGeometry hκ.le hs h00 hr U V := by
  let P := gammaGroundNativeFullMeasuredLiftBridge hκ.le hs hr hv U
  let Q := gammaGroundNativeFullMeasuredLiftBridge hκ.le hs hr hv V
  let fN := (P.comp hκ.le hs hr hv f).comp hκ.le hs hr hv (Q.symm hκ.le hs hr hv)
  have H := gammaNativeUnaryFullMeasured_original_base_geometry hκ hs h00 hr hv δ hδ hδ1
    (Section5.groundRVAt U.underlying) (Section5.groundRVAt V.underlying)
    (gammaGroundMeasuredNativeForm U) (gammaGroundMeasuredNativeForm V) fN
  exact (GammaUnaryMeasuredGeometry.iso ⟨asIso (gammaGroundNativeNormalizationHom U)⟩).trans
    (H.trans (.iso ⟨asIso (gammaGroundNativeNormalizationHom V).symm⟩))

theorem gammaGroundUnaryFullMeasured_original_base_kernel
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaGroundMeasuredRVObject hc B 1)
    (f : GammaFullMeasuredBijection (gammaGroundMeasuredObjectLift U) (gammaGroundMeasuredObjectLift V)) :
    gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V :=
  gammaUnaryMeasuredGeometry_principal
    (gammaGroundUnaryFullMeasured_original_base_geometry hκ hs h00 hr hv δ hδ hδ1 U V f)

end DiamondIntegral.Section3
