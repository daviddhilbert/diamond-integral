import «section 4».RESBoundedPsi
import «section 4».GammaBoundedSingletonProfiles

/-! The actual bounded singleton profile, after bounded psi, equals the
forgetful image of the actual measured RES value fibre. This verifies the
degree-one finite-Gamma balance in the concrete bounded target, without
asserting full tensor descent or category identification. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESBoundedFiniteBalancing
open GammaDefinableMaps GammaBoundedSingletonProfiles

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem psi_singleton_fibre (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    RESBoundedPsi.psi B k (GammaBoundedObjectPolynomial.objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k 1
      {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
      (constant_definable (n := 0) B α hα) (fun _ => β) (constant_definable B β hβ) (singleton_bounded α)) =
      RESOrdinaryReduction.forget B (RESChartRing.objectClass (RESFibreObjects.fibre B α β hα hβ)) :=
  (congrArg (RESBoundedPsi.psi B k)
    (objectPolynomial_singleton hc h00 linear hκ hs B hr hγ hΓ k α β hα hβ)).trans
    (RESBoundedPsi.psi_point_fibre B k α β hα hβ)

end DiamondIntegral.Section4.RESBoundedFiniteBalancing
