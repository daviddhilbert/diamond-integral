import «section 4».RESUnboundedPsi
import «section 4».GammaSingletonProfiles

/-! Actual degree-one finite-Gamma balancing in the concrete measured RES
quotient. The computed profile of a weighted Gamma singleton agrees with
the actual measured RV value-fibre class, by exactly the fibre ideal.
This is not a complete tensor-descent theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESFiniteBalancing
open RESMeasuredReduction RESUnboundedPsi GammaSingletonProfiles GammaObjectPolynomial GammaDefinableMaps

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem psi_singleton_fibre (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind)
    (α β : Values.Gamma (M := M)) (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    psi B k (objectPolynomial h00 hκ hs B hr hγ k 1 {z : Fin 1 → Values.Gamma (M := M) | z 0 = α}
      (constant_definable (n := 0) B α hα) (fun _ => β) (constant_definable B β hβ)) =
      quotient B (RESChartRing.objectClass (RESFibreObjects.fibre B α β hα hβ)) := by
  have hp := congrArg (psi B k) (objectPolynomial_singleton h00 hκ hs B hr hγ k α β hα hβ)
  have hv : psi B k (GammaUnboundedSpecialization.pointMonomial B k 1 (productName B α β hα hβ)) =
      weightedTorus B (productName B α β hα hβ) := by
    have h := psi_point_positive B k 1 (by decide) (productName B α β hα hβ)
    simpa only [Nat.sub_self, pow_zero, one_mul] using h
  exact hp.trans (hv.trans (fibre_class_eq_scaled B α β hα hβ).symm)

end DiamondIntegral.Section4.RESFiniteBalancing
