import «section 4».GammaOrdinaryAlgebras
import «section 4».GammaOrdinaryRESEvaluation
import Mathlib.RingTheory.TensorProduct.Maps

/-! The tensor of actual ordinary RES and Gamma rings over the actual
ordinary finite-Gamma ring. Both numerical Euler maps balance on that
whole coefficient ring; comparison and evaluation have actual pure-tensor
formulas. No RV tensor isomorphism or global descent is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryBalancedTensor
open GammaOrdinaryAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev Source (B : Base (M := M)) := RESOrdinaryRing.Ring B ⊗[Coeff B] GammaOrdinaryRing.Ring B
abbrev IntegerSource (B : Base (M := M)) := RESOrdinaryRing.Ring B ⊗[ℤ] GammaOrdinaryRing.Ring B

def resComparison (B : Base (M := M)) : RESOrdinaryRing.Ring B →ₐ[Coeff B] RVOrdinaryRing.Ring B where
  toRingHom := RVOrdinaryMaps.ofRES B
  commutes' _ := rfl

def gammaComparison (B : Base (M := M)) : GammaOrdinaryRing.Ring B →ₐ[Coeff B] RVOrdinaryRing.Ring B where
  toRingHom := GammaOrdinarySharpRingMap.sharp B
  commutes' c := (RingHom.congr_fun (GammaOrdinaryFiniteMaps.sharp_full_square B) c).symm

def comparison (B : Base (M := M)) : Source B →ₐ[Coeff B] RVOrdinaryRing.Ring B :=
  Algebra.TensorProduct.lift (resComparison B) (gammaComparison B) (fun _ _ => Commute.all _ _)

theorem comparison_tmul (B : Base (M := M)) (x : RESOrdinaryRing.Ring B) (y : GammaOrdinaryRing.Ring B) :
    comparison B (x ⊗ₜ[Coeff B] y) = RVOrdinaryMaps.ofRES B x * GammaOrdinarySharpRingMap.sharp B y := rfl

def resEvaluation (B : Base (M := M)) : RESOrdinaryRing.Ring B →ₐ[Coeff B] RESOrdinaryReduction.ReducedRing B where
  toRingHom := RESOrdinaryReduction.quotient B
  commutes' _ := rfl

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def gammaEvaluation (k : EulerKind) : GammaOrdinaryRing.Ring B →ₐ[Coeff B] RESOrdinaryReduction.ReducedRing B where
  toRingHom := GammaOrdinaryRESEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
  commutes' c := GammaOrdinaryRESEvaluation.finite_balance_apply h00 linear hκ hs B hr hγ hΓ k c

def evaluation (k : EulerKind) : Source B →ₐ[Coeff B] RESOrdinaryReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (resEvaluation B) (gammaEvaluation h00 linear hκ hs B hr hγ hΓ k) (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (k : EulerKind) (x : RESOrdinaryRing.Ring B) (y : GammaOrdinaryRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] y) = RESOrdinaryReduction.quotient B x *
      GammaOrdinaryRESEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k y := rfl

theorem evaluation_res (k : EulerKind) (x : RESOrdinaryRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] 1) = RESOrdinaryReduction.quotient B x := by
  rw [evaluation_tmul, map_one, mul_one]

theorem evaluation_gamma_chart (k : EulerKind) (x : RESOrdinaryRing.Ring B) {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[Coeff B] GammaOrdinaryRing.objectClass a) =
      RESOrdinaryReduction.quotient B x *
        ((GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B a.support a.support_definable) : RESOrdinaryReduction.ReducedRing B) *
          RESOrdinaryReduction.torusClass B ^ n) := by
  rw [evaluation_tmul, GammaOrdinaryRESEvaluation.evaluation_class]

end DiamondIntegral.Section4.RVOrdinaryBalancedTensor
