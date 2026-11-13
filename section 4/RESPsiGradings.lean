import «section 4».GammaPolynomialGradings
import «section 4».RESReductionGradings
import «section 4».RESUnboundedPsi
import «section 4».RESBoundedPsi
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! Both constructed psi homomorphisms preserve the actual gradings on
their whole polynomial sources. No RV tensor descent is assumed here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESPsiGradings
open RESReductionGradings GammaPolynomialGradings GammaNamesSubgroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem groupRingCharacter_mem (B : Base (M := M)) (a : DefinableGammaGroupRing B) :
    GammaUnboundedSpecialization.weightCharacter B (RESMeasuredReduction.weightCharacter B) a ∈
      measuredPiece B 0 := by
  rw [show GammaUnboundedSpecialization.weightCharacter B (RESMeasuredReduction.weightCharacter B) a =
      a.coeff.sum (fun b n => n • RESMeasuredReduction.weightCharacter B (Multiplicative.ofAdd b)) from
    AddMonoidAlgebra.lift_apply (RESMeasuredReduction.weightCharacter B) a]
  unfold Finsupp.sum
  apply (measuredPiece B 0).sum_mem
  intro b _
  apply (measuredPiece B 0).zsmul_mem
  rw [RESMeasuredReduction.weightCharacter_value]
  exact measured_weight_mem B _ b.property

theorem coefficientCharacter_mem (B : Base (M := M)) (k : EulerKind)
    (f : GammaDefinableConvolution.baseSubring B k) :
    GammaUnboundedSpecialization.coefficientCharacter B k (RESMeasuredReduction.weightCharacter B) f ∈
      measuredPiece B 0 := groupRingCharacter_mem B (GammaEndpointProjection.namedEndpoint B k f)

theorem measured_torus_pow_mem (B : Base (M := M)) (n : ℕ) :
    RESMeasuredReduction.torusClass B ^ n ∈ measuredPiece B n := by
  simpa only [smul_eq_mul, mul_one] using
    (SetLike.pow_mem_graded n (measured_torus_mem B))

theorem psi_unbounded_mem (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    {p : GammaFunctionPolynomial.sourceRing B k} (hp : p ∈ unboundedPiece B k n) :
    RESUnboundedPsi.psi B k p ∈ measuredPiece B n := by
  have he := (mem_unboundedPiece B k p n).mp hp
  unfold RESUnboundedPsi.psi
  rw [GammaUnboundedSpecialization.specialize_monomial B k (RESMeasuredReduction.weightCharacter B)
    (RESMeasuredReduction.torusClass B) p n (p.val.coeff n) he]
  simpa only [zero_add] using
    (SetLike.mul_mem_graded (coefficientCharacter_mem B k (p.val.coeff n)) (measured_torus_pow_mem B n))

theorem ordinary_torus_mem (B : Base (M := M)) :
    RESOrdinaryReduction.torusClass B ∈ ordinaryPiece B 1 := ordinary_class_mem B _

theorem ordinary_torus_pow_mem (B : Base (M := M)) (n : ℕ) :
    RESOrdinaryReduction.torusClass B ^ n ∈ ordinaryPiece B n := by
  simpa only [smul_eq_mul, mul_one] using
    (SetLike.pow_mem_graded n (ordinary_torus_mem B))

theorem ordinary_intCast_mem (B : Base (M := M)) (z : ℤ) :
    (z : RESOrdinaryReduction.ReducedRing B) ∈ ordinaryPiece B 0 := by
  change (ordinaryCoaction B).map (z : RESOrdinaryReduction.ReducedRing B) = Polynomial.monomial 0 (z : RESOrdinaryReduction.ReducedRing B)
  simp

theorem psi_bounded_mem (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    {p : GammaBoundedPolynomial.sourceRing B k} (hp : p ∈ boundedPiece B k n) :
    RESBoundedPsi.psi B k p ∈ ordinaryPiece B n := by
  have he := (mem_boundedPiece B k p n).mp hp
  unfold RESBoundedPsi.psi
  rw [GammaBoundedSpecialization.specialize_monomial B k (RESOrdinaryReduction.torusClass B) p n (p.val.coeff n) he]
  simpa only [zero_add] using (SetLike.mul_mem_graded
    (ordinary_intCast_mem B (GammaBoundedFunctions.baseBoundedEuler B k (p.val.coeff n)))
    (ordinary_torus_pow_mem B n))

def gradedUnboundedPsi (B : Base (M := M)) (k : EulerKind) :
    GradedRingHom (unboundedPiece B k) (measuredPiece B) where
  toRingHom := RESUnboundedPsi.psi B k
  map_mem := psi_unbounded_mem B k

def gradedBoundedPsi (B : Base (M := M)) (k : EulerKind) :
    GradedRingHom (boundedPiece B k) (ordinaryPiece B) where
  toRingHom := RESBoundedPsi.psi B k
  map_mem := psi_bounded_mem B k

end DiamondIntegral.Section4.RESPsiGradings
