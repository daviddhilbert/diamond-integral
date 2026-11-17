import «section 3».GammaMeasuredMonotoneBases
import «section 3».GammaPrincipalGeometricReflection
import «section 3».GammaLastGeometryBaseReduction

/-! The principal quotient reflects homogeneous equalities through
definable enlargement of the real and Gamma names. Finite geometry is
reflected in the larger base and its names are then eliminated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)} {n : ℕ}

theorem GammaLastMeasuredGeometry.principal_sound
    {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
    {h00 : M ⊨ Axioms.ACVF00} {hr : Cardinal.mk B.real < κ}
    {U V : GammaGroundMeasuredRVObject hc B (n+1)} (h : GammaLastMeasuredGeometry hκ hs h00 hr U V) :
    gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V := by
  induction h with
  | iso e => obtain ⟨e⟩ := e; exact gammaMeasuredPrincipalValue_iso e.hom
  | elementary U hAd =>
    exact (gammaGroundMeasuredRVSpecialCongruence hc B).eq.mpr
      (gammaMeasuredElementaryObject_congruence hκ hs h00 hr U hAd)
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | coprod h k ih ik =>
    have hAdd (A D : GammaGroundMeasuredRVObject hc B (n+1)) :=
      gammaMeasuredPrincipalValue_add (gammaGroundMeasuredRVClass_coprod A D)
    rw [hAdd,hAdd,ih,ik]

theorem gammaPrincipal_monoBase_reflect
    (hReal : B.real ⊆ C.real) (hGamma : B.gamma ⊆ C.gamma)
    (H : GammaDefinableBaseReduction C B)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hrC : Cardinal.mk C.real < κ) (hrB : Cardinal.mk B.real < κ)
    {U V : GammaGroundMeasuredRVObject hc B (n+1)}
    (h : gammaMeasuredPrincipalValue (U.monoBase hReal hGamma) =
      gammaMeasuredPrincipalValue (V.monoBase hReal hGamma)) :
    gammaMeasuredPrincipalValue U = gammaMeasuredPrincipalValue V := by
  have hG := gammaLastMeasuredGeometry_of_native (gammaPrincipal_geometric_reflection hκ hs h00 hrC h)
  have hR := gammaLastMeasuredGeometry_reduce hκ hs h00 hrC hrB H hG
  rw [gammaMeasuredRV_reduce_monoBase,gammaMeasuredRV_reduce_monoBase] at hR
  exact hR.principal_sound

end DiamondIntegral.Section3
