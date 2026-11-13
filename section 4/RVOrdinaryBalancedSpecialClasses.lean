import «section 4».RVOrdinaryBalancedGradings
import «section 4».RVOrdinaryPNormalization
import «section 4».GammaOrdinarySpecialClasses
import «section 4».RVOrdinaryZeroCount

/-! The actual degree-one point and P preimages in the ordinary balanced
tensor, with comparison and Euler values. Its degree-zero finite count
proves the source nontrivial, without proving the degree-one point nonzero. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryBalancedSpecialClasses
open GammaOrdinaryAlgebras RVOrdinaryBalancedTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rayClass (B : Base (M := M)) : GammaOrdinaryRing.Ring B :=
  GammaOrdinaryRing.objectClass (GammaOrdinaryCharts.ofWeighted (RVMeasuredSpecialClasses.rayChart B))
def pointPreimage (B : Base (M := M)) : Source B := RESOrdinaryRing.objectClass (RESFibreObjects.point B) ⊗ₜ[Coeff B] 1
def pPreimage (B : Base (M := M)) : Source B := pointPreimage B - (1 ⊗ₜ[Coeff B] rayClass B)

theorem pointPreimage_mem (B : Base (M := M)) : pointPreimage B ∈ RVOrdinaryBalancedGradings.piece B 1 :=
  RVOrdinaryBalancedGradings.tmul_mem B (RESOrdinaryGrading.class_mem B (RESFibreObjects.point B)) (SetLike.one_mem_graded _)

theorem pPreimage_mem (B : Base (M := M)) : pPreimage B ∈ RVOrdinaryBalancedGradings.piece B 1 :=
  (RVOrdinaryBalancedGradings.piece B 1).sub_mem (pointPreimage_mem B)
    (RVOrdinaryBalancedGradings.tmul_mem B (SetLike.one_mem_graded _) (GammaOrdinaryGrading.class_mem B _))

theorem comparison_pPreimage (B : Base (M := M)) : comparison B (pPreimage B) = RVOrdinaryPNormalization.pClass B := by
  unfold pPreimage pointPreimage rayClass
  rw [map_sub, comparison_tmul, comparison_tmul, map_one, map_one, mul_one, one_mul,
    RVOrdinaryMaps.ofRES_class, GammaOrdinarySharpRingMap.sharp_class]
  rfl

def zeroCount (B : Base (M := M)) : Source B →+* ℤ := (RVOrdinaryZeroCount.full B).comp (comparison B).toRingHom

theorem zero_ne_one (B : Base (M := M)) : (0 : Source B) ≠ 1 := by
  intro h
  have he : (0 : ℤ) = 1 := by simpa only [map_zero, map_one] using congrArg (zeroCount B) h
  exact _root_.zero_ne_one he

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem evaluation_ray (k : EulerKind) :
    GammaOrdinaryRESEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (rayClass B) =
      (k.rayValue : RESOrdinaryReduction.ReducedRing B) * RESOrdinaryReduction.torusClass B := by
  rw [rayClass, GammaOrdinaryRESEvaluation.evaluation_class]
  change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k 1
    (GammaIndicators.indicatorFamily B GammaCounterweightedRay.positiveRay (GammaCounterweightedRay.positiveRay_definable B)) : RESOrdinaryReduction.ReducedRing B) *
      RESOrdinaryReduction.torusClass B ^ 1 = _
  rw [GammaOrdinarySpecialClasses.positiveRay_integral h00 linear hκ hs B hr hγ hΓ k, pow_one]

theorem evaluation_point (k : EulerKind) : evaluation h00 linear hκ hs B hr hγ hΓ k (pointPreimage B) = RESOrdinaryReduction.pointClass B :=
  evaluation_res h00 linear hκ hs B hr hγ hΓ k (RESOrdinaryRing.objectClass (RESFibreObjects.point B))

theorem evaluation_p (k : EulerKind) : evaluation h00 linear hκ hs B hr hγ hΓ k (pPreimage B) =
    RESOrdinaryReduction.pointClass B - (k.rayValue : RESOrdinaryReduction.ReducedRing B) * RESOrdinaryReduction.torusClass B := by
  rw [pPreimage, map_sub, evaluation_point, evaluation_tmul, map_one, one_mul, evaluation_ray]

theorem evaluation_p_geometric : evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (pPreimage B) =
    RESOrdinaryReduction.pointClass B + RESOrdinaryReduction.torusClass B := by
  simpa only [EulerKind.rayValue, Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add] using
    evaluation_p h00 linear hκ hs B hr hγ hΓ EulerKind.geometric

theorem evaluation_p_bounded : evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (pPreimage B) = RESOrdinaryReduction.pointClass B := by
  simpa only [EulerKind.rayValue, Int.cast_zero, zero_mul, sub_zero] using evaluation_p h00 linear hκ hs B hr hγ hΓ EulerKind.bounded

theorem evaluation_surjective (k : EulerKind) : Function.Surjective (evaluation h00 linear hκ hs B hr hγ hΓ k) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨x ⊗ₜ[Coeff B] 1, evaluation_res h00 linear hκ hs B hr hγ hΓ k x⟩

end DiamondIntegral.Section4.RVOrdinaryBalancedSpecialClasses
