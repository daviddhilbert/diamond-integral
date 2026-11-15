import «section 4».RVT001OrdinaryDescent
import «section 4».Section3T001Integration
import «section 4».RESDimensionFreeReduction
import «section 4».RESHomogenization

/-! The bounded RV retraction into the actual ungraded reduced RES ring.
The T001 presentation is instantiated from the proved Section 3 transport.
Arbitrary finite-to-one RV labels disappear by actual point padding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
open scoped TensorProduct
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def nativeRVEvaluation (k : EulerKind) : RVOrdinaryRing.Ring B →+* RESDimensionFreeReduction.Ring B :=
  (RESDimensionFreeReduction.fromGradedReduced B).comp
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ
      (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hr hγ hΓ) k)

theorem nativeRVEvaluation_res (k : EulerKind) (x : RESOrdinaryRing.Ring B) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ k (RVOrdinaryMaps.ofRES B x) =
      RESDimensionFreeReduction.fromOrdinary B x := by
  unfold nativeRVEvaluation
  rw [RingHom.comp_apply, RVT001OrdinaryDescent.evaluation_res,
    RESDimensionFreeReduction.fromGradedReduced_raw]

def nativeTorusClass : RESDimensionFreeReduction.Ring B :=
  RESDimensionFreeReduction.fromGradedReduced B (RESOrdinaryReduction.torusClass B)

theorem nativeRVEvaluation_gamma (k : EulerKind) {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ k
      (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a)) =
      (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n
        (GammaIndicators.indicatorFamily B a.support a.support_definable) : RESDimensionFreeReduction.Ring B) *
          nativeTorusClass B ^ n := by
  have he : RVOrdinaryBalancedTensor.comparison B
      ((1 : RESOrdinaryRing.Ring B) ⊗ₜ[GammaOrdinaryAlgebras.Coeff B]
        GammaOrdinaryRing.objectClass a) =
      GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a) := by
    rw [RVOrdinaryBalancedTensor.comparison_tmul, map_one, one_mul]
  unfold nativeRVEvaluation
  rw [RingHom.comp_apply, ← he, RVT001OrdinaryDescent.evaluation_comparison,
    RVOrdinaryBalancedTensor.evaluation_gamma_chart, map_one, one_mul, map_mul, map_intCast, map_pow]
  rfl

theorem nativeRVEvaluation_point (k : EulerKind) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ k
      (RVOrdinaryRing.objectClass (RESPointTuples.chart B 1)) = 1 := by
  have he : RVOrdinaryMaps.ofRES B (RESOrdinaryRing.objectClass (RESPointTuples.res B 1)) =
      RVOrdinaryRing.objectClass (RESPointTuples.chart B 1) :=
    RVOrdinaryMaps.ofRES_class B (RESPointTuples.res B 1)
  rw [← he, nativeRVEvaluation_res]
  have hp : RESDimensionFreeRing.quotient B
      (RESOrdinaryRing.objectClass (RESPointTuples.res B 1)) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one (RESDimensionFreeRing.quotient B), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RESDimensionFreeRing.point_minus_one_mem B)
  change RESDimensionFreeReduction.quotient B
    (RESDimensionFreeRing.quotient B (RESOrdinaryRing.objectClass (RESPointTuples.res B 1))) = 1
  rw [hp, map_one]

def castRVChart {k l : ℕ} (h : k = l) (a : RVMeasuredCharts.Chart B k) : RVMeasuredCharts.Chart B l := h ▸ a

theorem ordinary_castRVChart {k l : ℕ} (h : k = l) (a : RVMeasuredCharts.Chart B k) :
    RVOrdinaryRing.objectClass (castRVChart B h a) = RVOrdinaryRing.objectClass a := by
  cases h
  rfl

def castRVTarget {k l n : ℕ} {a : RVMeasuredCharts.Chart B k} {b : RVMeasuredCharts.Chart B l}
    (h : l = n) (F : RVUnderlyingIsomorphisms.Iso a b) :
    RVUnderlyingIsomorphisms.Iso a (castRVChart B h b) := by
  cases h
  exact F

theorem ordinary_RV_homogenization {k l : ℕ} (a : RVMeasuredCharts.Chart B k)
    (b : RVMeasuredCharts.Chart B l) (F : RVUnderlyingIsomorphisms.Iso a b) :
    RVOrdinaryRing.objectClass a * RVOrdinaryRing.objectClass (RESPointTuples.chart B 1) ^ l =
      RVOrdinaryRing.objectClass b * RVOrdinaryRing.objectClass (RESPointTuples.chart B 1) ^ k := by
  let H := RVUnderlyingProducts.productIso F (RESPointTuples.underlyingIso B l k)
  have he := RVOrdinaryRing.objectClass_iso
    (RVUnderlyingIsomorphisms.toFixed (castRVTarget B (Nat.add_comm k l) H))
  rw [ordinary_castRVChart, RVOrdinaryRing.objectClass_product, RVOrdinaryRing.objectClass_product] at he
  have hp (n : ℕ) : RVOrdinaryRing.objectClass (RESPointTuples.chart B n) =
      RVOrdinaryRing.objectClass (RESPointTuples.chart B 1) ^ n := by
    have hh := congrArg (RVOrdinaryMaps.ofRES B) (RESPointTuples.ordinary_power B n)
    simpa only [RVOrdinaryMaps.ofRES_class, map_pow, RESPointTuples.res] using hh
  rw [hp l, hp k] at he
  exact he

theorem nativeRVEvaluation_underlyingIso (kind : EulerKind) {k l : ℕ}
    (a : RVMeasuredCharts.Chart B k) (b : RVMeasuredCharts.Chart B l)
    (F : RVUnderlyingIsomorphisms.Iso a b) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass a) =
      nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (RVOrdinaryRing.objectClass b) := by
  have he := congrArg (nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind)
    (ordinary_RV_homogenization B a b F)
  simpa only [map_mul, map_pow, nativeRVEvaluation_point, one_pow, mul_one] using he

end DiamondIntegral.Section5
