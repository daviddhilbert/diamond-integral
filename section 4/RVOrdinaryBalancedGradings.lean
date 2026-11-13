import «section 4».RVOrdinaryBalancedTensor
import «section 4».GammaOrdinaryFiniteMapGradings
import «section 4».RVOrdinaryMapGradings
import «section 4».TensorGradedMaps

/-! Full grading of the actual ordinary RES/Gamma tensor. Homogeneous
pure tensors have the sum degree; comparison and both numerical Euler
evaluations preserve degree on the entire tensor. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryBalancedGradings
open GammaOrdinaryAlgebras RVOrdinaryBalancedTensor
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def data (B : Base (M := M)) : TensorPolynomialCoaction.Data (Coeff B) (RESOrdinaryRing.Ring B) (GammaOrdinaryRing.Ring B) where
  base := GammaOrdinaryFiniteGrading.gradingCoaction B
  left := RESOrdinaryGrading.gradingCoaction B
  right := GammaOrdinaryGrading.gradingCoaction B
  left_compatible := (GammaOrdinaryFiniteGrading.gradingCoaction B).map_coaction_of_mem (RESOrdinaryGrading.gradingCoaction B)
    (algebraMap (Coeff B) (RESOrdinaryRing.Ring B)) (fun _ _ hx => GammaOrdinaryFiniteMapGradings.sharp_mem B hx)
  right_compatible := (GammaOrdinaryFiniteGrading.gradingCoaction B).map_coaction_of_mem (GammaOrdinaryGrading.gradingCoaction B)
    (algebraMap (Coeff B) (GammaOrdinaryRing.Ring B)) (fun _ _ hx => GammaOrdinaryFiniteMapGradings.full_mem B hx)

def coaction (B : Base (M := M)) : PolynomialCoactionGrading.Coaction (Source B) := TensorCoactionGrading.coaction (data B)
def piece (B : Base (M := M)) (n : ℕ) : AddSubgroup (Source B) := (coaction B).piece n
instance gradedRing (B : Base (M := M)) : GradedRing (piece B) := (coaction B).grading

theorem tmul_mem (B : Base (M := M)) {m n : ℕ} {x : RESOrdinaryRing.Ring B} {y : GammaOrdinaryRing.Ring B}
    (hx : x ∈ RESOrdinaryGrading.gradedPiece B m) (hy : y ∈ GammaOrdinaryGrading.gradedPiece B n) :
    x ⊗ₜ[Coeff B] y ∈ piece B (m + n) := TensorCoactionGrading.tmul_mem (data B) hx hy

def gradedComparison (B : Base (M := M)) : GradedRingHom (piece B) (RVOrdinaryGrading.gradedPiece B) :=
  TensorGradedMaps.gradedMap (data B) (RVOrdinaryGrading.gradingCoaction B) (comparison B).toRingHom (by
    intro m n x y hx hy
    change comparison B (x ⊗ₜ[Coeff B] y) ∈ RVOrdinaryGrading.gradedPiece B (m + n)
    rw [comparison_tmul]
    exact SetLike.mul_mem_graded (RVOrdinaryMapGradings.ofRES_mem B hx) (GammaOrdinarySharpRingMap.sharp_mem B hy))

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def gradedEvaluation (k : EulerKind) : GradedRingHom (piece B) (RESReductionGradings.ordinaryPiece B) :=
  TensorGradedMaps.gradedMap (data B) (RESReductionGradings.ordinaryCoaction B)
    (evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom (by
      intro m n x y hx hy
      change evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] y) ∈ RESReductionGradings.ordinaryPiece B (m + n)
      rw [evaluation_tmul]
      exact SetLike.mul_mem_graded (RESReductionGradings.ordinary_quotient_mem B hx)
        (GammaOrdinaryRESEvaluation.evaluation_mem h00 linear hκ hs B hr hγ hΓ k hy))

end DiamondIntegral.Section4.RVOrdinaryBalancedGradings
