import «section 4».RVOrdinaryTensorForget
import «section 4».GammaOrdinaryRadius
import «section 4».RVBalancedRadiusChoices
import «section 4».RVBalancedRadiusQuotient
import «section 4».RVBoundedOrdinaryEvaluation

/-! The bounded measured tensor maps to the actual full ordinary tensor.
All accepted radius preimages vanish there already, by ordinary Gamma
annulus cancellation and ordinary RES point isomorphisms. Thus the map
factors through the bounded source-radius quotient, preserving degree.
This does not identify that source quotient with an RV quotient. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryBoundedTensorForget
open GammaRVLifts RVRadiusGenerators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def forget (B : Base (M := M)) : RVBoundedBalancedTensor.Source B →+* RVOrdinaryBalancedTensor.Source B :=
  (RVOrdinaryTensorForget.forget B).comp (RVBoundedTensorComparison.toFull B).toRingHom

theorem forget_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    forget B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      RESOrdinaryRing.forget B x ⊗ₜ[GammaOrdinaryAlgebras.Coeff B]
        GammaOrdinaryRing.forget B (GammaBoundedRVMaps.forget B y) :=
  RVOrdinaryTensorForget.forget_tmul B x (GammaBoundedRVMaps.forget B y)

theorem withLift_zero (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) :
    forget B (RVBalancedRadiusChoices.withLift B γ hγ t) = 0 := by
  rw [RVBalancedRadiusChoices.withLift_formula, map_sub, map_add,
    forget_tmul, forget_tmul, forget_tmul, map_one, map_one, map_one,
    GammaBoundedRVMaps.forget_class, GammaOrdinaryRing.forget_class,
    RESOrdinaryRing.forget_objectClass, RESOrdinaryRing.forget_objectClass]
  change (1 ⊗ₜ[GammaOrdinaryAlgebras.Coeff B]
      GammaOrdinaryRing.objectClass (GammaOrdinaryRadius.annulus B γ hγ)) +
    (RESOrdinaryRing.objectClass (RVPointChoices.pointRESChart B t.point t.definable) ⊗ₜ[GammaOrdinaryAlgebras.Coeff B] 1) -
    (RESOrdinaryRing.objectClass (RVPointChoices.pointRESChart B oneCode (oneCode_definable B)) ⊗ₜ[GammaOrdinaryAlgebras.Coeff B] 1) = 0
  rw [GammaOrdinaryRadius.annulus_zero B γ hγ t, TensorProduct.tmul_zero, zero_add,
    RESOrdinaryPoints.point_classes B t.point oneCode t.definable (oneCode_definable B), sub_self]

theorem radius_zero (B : Base (M := M)) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    forget B (RVBalancedSpecialClasses.radiusPreimage B γ hγ) = 0 := by
  rw [RVBalancedRadiusChoices.canonical_eq_withLift B γ hγ (Classical.choice (radiusLift_exists B γ hγ))]
  exact withLift_zero B γ hγ _

theorem radiusIdeal_le_ker (B : Base (M := M)) :
    RVBalancedRadiusIdeal.radiusIdeal B ≤ RingHom.ker (forget B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  exact radius_zero B γ hγ

def fromRadius (B : Base (M := M)) : RVBalancedRadiusQuotient.Ring B →+* RVOrdinaryBalancedTensor.Source B :=
  Ideal.Quotient.lift _ (forget B) (radiusIdeal_le_ker B)

theorem fromRadius_mk (B : Base (M := M)) (x : RVBoundedBalancedTensor.Source B) :
    fromRadius B (RVBalancedRadiusQuotient.quotient B x) = forget B x := rfl

def gradedForget (B : Base (M := M)) :
    GradedRingHom (RVBalancedGradings.boundedPiece B) (RVOrdinaryBalancedGradings.piece B) :=
  (RVOrdinaryTensorForget.gradedForget B).comp (RVBoundedTensorComparison.gradedToFull B)

def gradedFromRadius (B : Base (M := M)) :
    GradedRingHom (RVBalancedRadiusQuotient.piece B) (RVOrdinaryBalancedGradings.piece B) :=
  (RVBalancedGradings.boundedCoaction B).gradedQuotientLift (RVOrdinaryBalancedGradings.coaction B)
    (forget B) (RVBalancedRadiusIdeal.radiusIdeal B) (RVBalancedRadiusQuotient.ideal_coefficients B)
    (fun x hx => radiusIdeal_le_ker B hx) (fun _ _ hx => (gradedForget B).map_mem hx)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_square (k : EulerKind) :
    (RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.comp (forget B) =
      (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom := by
  change ((RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom.comp
    (RVOrdinaryTensorForget.forget B)).comp (RVBoundedTensorComparison.toFull B).toRingHom = _
  rw [RVOrdinaryTensorForget.evaluation_square]
  rfl

end DiamondIntegral.Section4.RVOrdinaryBoundedTensorForget
