import «section 5».NativeRVSetValues
import «section 3».GammaGroundRVFinitePartitions
import «section 4».Section3RVChartRingMaps

/-! The native bounded retraction respects actual object products and
finite partitions, while forgetting every finite label via actual maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

def nativeGroundRVEvaluation : GammaGroundRVGrothendieckRing hc B →+* RESDimensionFreeReduction.Ring B :=
  (nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind).comp (Section3RVChartRingMaps.ordinary hc B)

theorem nativeGroundRVEvaluation_class {k : ℕ} (U : GammaGroundRVObject hc B k) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) =
      nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) := by
  unfold nativeGroundRVEvaluation
  rw [RingHom.comp_apply, Section3RVChartRingMaps.ordinary_class]

theorem nativeGroundRVEvaluation_bijection {k l : ℕ}
    (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l)
    (f : GammaGroundBijection U.domain V.domain) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) =
      nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass V) := by
  rw [nativeGroundRVEvaluation_class, nativeGroundRVEvaluation_class]
  exact nativeRVEvaluation_underlyingIso h00 linear hκ hs hc B hr hγ hΓ kind _ _ (nativeRVObjectUnderlyingIso f)

theorem nativeGroundRVEvaluation_product {k l : ℕ}
    (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass (U.product V)) =
      nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) *
      nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass V) := by
  have he : ordinaryClass (U.product V) = ordinaryClass U * ordinaryClass V := by
    simp only [ordinaryClass, gammaGroundRVSemiringClass_product]
    exact (of_mul_of _ _).symm
  rw [he, map_mul]

theorem nativeGroundRVEvaluation_finite_partition {k : ℕ} {ι : Type} [Fintype ι]
    (U : GammaGroundRVObject hc B k)
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) U.arity))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ U.domain.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) =
      ∑ i, nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (ordinaryClass (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩))) := by
  have he := congrArg (of : GammaGroundRVPositiveSemiring hc B → GammaGroundRVGrothendieckRing hc B)
    (gammaGroundRVSemiringClass_finite_partition U A hd hcov)
  change ordinaryClass U = _ at he
  simp only [map_sum] at he
  exact (congrArg (nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind) he).trans (map_sum _ _ _)

end DiamondIntegral.Section5
