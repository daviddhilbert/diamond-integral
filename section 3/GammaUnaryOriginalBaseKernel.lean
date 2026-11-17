import «section 3».GammaUnaryOriginalBaseGeometry
import «section 3».GammaMeasuredIndexedGeometry

/-! The full unary measured kernel comparison descends to an arbitrary
original base. No coefficient-field closure remains in its hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaUnaryMeasuredGeometry_principal
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {h00 : M ⊨ Axioms.ACVF00} {hr : Cardinal.mk B.real < κ}
    {U V : GammaGroundMeasuredRVObject hc B 1} (h : GammaUnaryMeasuredGeometry hκ hs h00 hr U V) :
    gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V := by
  induction h with
  | iso e => obtain ⟨e⟩ := e; exact gammaMeasuredPrincipalValue_iso e.hom
  | elementary U hAd =>
    exact (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr
      (gammaMeasuredElementaryObject_congruence hκ hs h00 hr U hAd)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | @coprod U V X Y h₁ h₂ ih₁ ih₂ =>
    have hLeft := gammaMeasuredPrincipalValue_add (gammaGroundMeasuredRVClass_coprod U X)
    have hRight := gammaMeasuredPrincipalValue_add (gammaGroundMeasuredRVClass_coprod V Y)
    exact hLeft.trans ((congrArg₂ (· + ·) ih₁ ih₂).trans hRight.symm)

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeUnaryFullMeasured_original_base_kernel
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U V : GammaObjectAt B Set.univ 1)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η)) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V η :=
  gammaUnaryMeasuredGeometry_principal
    (gammaNativeUnaryFullMeasured_original_base_geometry hκ hs h00 hr hv δ hδ hδ1 U V ω η f)

end DiamondIntegral.Section3
