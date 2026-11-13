import «section 3».GammaGroundPiecewiseGLZ
import «section 3».GammaGroundUnitFamilyFullLift
import «section 3».GammaGroundUnitFamilyCodeTransport
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}
variable {A D : GammaGroundGammaObject hc B n}

/-- The piecewise-GL(Z) criterion constructs a genuine full-preimage
Gamma morphism, with its prescribed interpreted family bijection.
This direction uses no classification input. -/
theorem gammaGroundGammaHom_of_piecewiseGLZ {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (H : GammaGroundFamilyBijection A D) (hH : GammaGroundPiecewiseGLZ H) :
    ∃ g : GammaGroundGammaHom A D, g.bijection = H := by
  obtain ⟨L,hL⟩ := gammaGroundUnitFamily_affine_full_lift hκ hs hsmall hγsmall A D H
    (gammaGroundPiecewiseGLZ_pointwise H hH)
  exact ⟨gammaGroundGammaHomOfUnitFamilyLift H L hL,rfl⟩

end DiamondIntegral.Section3
