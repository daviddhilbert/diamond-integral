import «section 4».IntrinsicBalancedGradings
import «section 4».IntrinsicQuotientGradings
import «section 4».RVBoundedOrdinaryEvaluation

/-! Actual graded Euler evaluations on the intrinsic balanced tensors.
They retain the original parameter base and the explicit cited-linearity
input. The bounded evaluation needs no canonical-structure premise and
is independent of Euler choice. Global descent through the RV comparison
kernel is a separate obligation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.IntrinsicBalancedEvaluations
open RingPresentationTransport IntrinsicFiniteGammaAlgebras IntrinsicBalancedTensors
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def measuredLeft (B : Base (M := M)) : RESDisjointPresentation.Ring B →+* RESDisjointReduction.Measured.Ring B :=
  transport (RESDisjointPresentation.equivalence B) (RESDisjointReduction.Measured.equivalence B) (RESMeasuredReduction.quotient B)

def ordinaryLeft (B : Base (M := M)) : RESDisjointPresentation.Ring B →+* RESDisjointReduction.Ordinary.Ring B :=
  transport (RESDisjointPresentation.equivalence B) (RESDisjointReduction.Ordinary.equivalence B) (RESOrdinaryReduction.forget B)

theorem measuredLeft_eq (B : Base (M := M)) : measuredLeft B = RESDisjointReduction.Measured.quotient B := by
  apply DFunLike.ext
  intro x
  exact transport_value (RESDisjointPresentation.equivalence B) (RESDisjointReduction.Measured.equivalence B)
    (RESMeasuredReduction.quotient B) x (RESDisjointReduction.Measured.quotient B x)
    (RESDisjointReduction.Measured.equivalence_quotient B x).symm

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def measuredGamma (k : EulerKind) : GammaRVFiniteUnionPresentation.Ring B →+* RESDisjointReduction.Measured.Ring B :=
  transport (GammaRVFiniteUnionPresentation.equivalence B) (RESDisjointReduction.Measured.equivalence B)
    (GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom

def boundedGamma (k : EulerKind) : GammaBoundedRVFiniteUnionPresentation.Ring B →+* RESDisjointReduction.Ordinary.Ring B :=
  transport (GammaBoundedRVFiniteUnionPresentation.equivalence B) (RESDisjointReduction.Ordinary.equivalence B)
    ((GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).comp (GammaBoundedRVMaps.forget B))

def measured (k : EulerKind) : Source B →+* RESDisjointReduction.Measured.Ring B :=
  transport (equivalence B).toRingEquiv (RESDisjointReduction.Measured.equivalence B)
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom

def bounded (k : EulerKind) : BoundedSource B →+* RESDisjointReduction.Ordinary.Ring B :=
  transport (boundedEquivalence B).toRingEquiv (RESDisjointReduction.Ordinary.equivalence B)
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom

theorem measured_tmul (k : EulerKind) (x : RESDisjointPresentation.Ring B) (y : GammaRVFiniteUnionPresentation.Ring B) :
    measured h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] y) =
      measuredLeft B x * measuredGamma h00 linear hκ hs B hr hγ hΓ k y := by
  change (RESDisjointReduction.Measured.equivalence B).symm
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k (equivalence B (x ⊗ₜ[Coeff B] y))) = _
  rw [equivalence_tmul, RVFiniteBalancedTensor.evaluation_tmul, map_mul]
  rfl

theorem bounded_tmul (k : EulerKind) (x : RESDisjointPresentation.Ring B) (y : GammaBoundedRVFiniteUnionPresentation.Ring B) :
    bounded h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] y) =
      ordinaryLeft B x * boundedGamma h00 linear hκ hs B hr hγ hΓ k y := by
  change (RESDisjointReduction.Ordinary.equivalence B).symm
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (boundedEquivalence B (x ⊗ₜ[Coeff B] y))) = _
  rw [boundedEquivalence_tmul, RVBoundedOrdinaryEvaluation.evaluation_tmul, map_mul]
  rfl

theorem measured_mem (k : EulerKind) {n : ℕ} {x : Source B} (hx : x ∈ IntrinsicBalancedGradings.measuredPiece B n) :
    measured h00 linear hκ hs B hr hγ hΓ k x ∈ IntrinsicQuotientGradings.MeasuredRES.piece B n := by
  apply (IntrinsicQuotientGradings.MeasuredRES.equivalence_mem_iff B n _).mp
  change (RESDisjointReduction.Measured.equivalence B) ((RESDisjointReduction.Measured.equivalence B).symm
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k (equivalence B x))) ∈ RESReductionGradings.measuredPiece B n
  rw [RingEquiv.apply_symm_apply]
  exact (RVBalancedMapGradings.gradedMeasuredEvaluation h00 linear hκ hs B hr hγ hΓ k).map_mem
    (IntrinsicBalancedGradings.equivalence_mem B hx)

theorem bounded_mem (k : EulerKind) {n : ℕ} {x : BoundedSource B} (hx : x ∈ IntrinsicBalancedGradings.boundedPiece B n) :
    bounded h00 linear hκ hs B hr hγ hΓ k x ∈ IntrinsicQuotientGradings.OrdinaryRES.piece B n := by
  apply (IntrinsicQuotientGradings.OrdinaryRES.equivalence_mem_iff B n _).mp
  change (RESDisjointReduction.Ordinary.equivalence B) ((RESDisjointReduction.Ordinary.equivalence B).symm
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (boundedEquivalence B x))) ∈ RESReductionGradings.ordinaryPiece B n
  rw [RingEquiv.apply_symm_apply]
  exact (RVBoundedOrdinaryEvaluation.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).map_mem
    (IntrinsicBalancedGradings.boundedEquivalence_mem B hx)

def gradedMeasured (k : EulerKind) : GradedRingHom (IntrinsicBalancedGradings.measuredPiece B) (IntrinsicQuotientGradings.MeasuredRES.piece B) where
  toRingHom := measured h00 linear hκ hs B hr hγ hΓ k
  map_mem := fun hx => measured_mem h00 linear hκ hs B hr hγ hΓ k hx

def gradedBounded (k : EulerKind) : GradedRingHom (IntrinsicBalancedGradings.boundedPiece B) (IntrinsicQuotientGradings.OrdinaryRES.piece B) where
  toRingHom := bounded h00 linear hκ hs B hr hγ hΓ k
  map_mem := fun hx => bounded_mem h00 linear hκ hs B hr hγ hΓ k hx

theorem bounded_independent_kind (k l : EulerKind) : bounded h00 linear hκ hs B hr hγ hΓ k = bounded h00 linear hκ hs B hr hγ hΓ l := by
  apply DFunLike.ext
  intro x
  change (RESDisjointReduction.Ordinary.equivalence B).symm
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (boundedEquivalence B x)) =
    (RESDisjointReduction.Ordinary.equivalence B).symm
    (RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ l (boundedEquivalence B x))
  rw [RVBoundedOrdinaryEvaluation.evaluation_independent_kind h00 linear hκ hs B hr hγ hΓ k l]

theorem measured_on_res (k : EulerKind) (x : RESDisjointPresentation.Ring B) :
    measured h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] 1) = RESDisjointReduction.Measured.quotient B x := by
  rw [measured_tmul, map_one, mul_one, measuredLeft_eq]

theorem bounded_on_res (k : EulerKind) (x : RESDisjointPresentation.Ring B) :
    bounded h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] 1) = ordinaryLeft B x := by
  rw [bounded_tmul, map_one, mul_one]

end DiamondIntegral.Section4.IntrinsicBalancedEvaluations
