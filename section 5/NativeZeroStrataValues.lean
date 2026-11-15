import «section 5».NativeFullKeySelections
import «section 5».NativeZeroStrataPullbacks
import «section 5».NativeRVSetArithmetic

/-! The actual positive RV representatives of the zero strata recover
the raw RV value of the full key image. This works for both Euler kinds;
geometric degree normalization is applied separately to each lift degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem nativeFullKeyDrop_value
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) {d : ℕ} (j : Fin d → Fin n)
    (hz : ∀ a : A,∀ i : Fin n,i ∉ Set.range j → a.val.1 i = 0) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (nativeMixedFullKeyMap (nativeVFCoordinateSelection A j).image).image =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (nativeMixedFullKeyMap A).image :=
  (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (nativeFullKeyDropBijection A j hz)).symm

theorem nativeVFZeroStratumRVObject_raw_value
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) (I : Finset (Fin n)) :
    nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart
          (nativeVFZeroStratumRVObject hκ hs h00 hr A hpull hf I))) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r) I) := by
  let U := nativeVFZeroStratumRVObject hκ hs h00 hr A hpull hf I
  have he : nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (nativeMixedFullKeyMap (nativeVFCoordinateSelection (nativeVFZeroStratum A I)
          (nativeVFZeroPatternIndex I)).image).image :=
    ((nativeRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ kind U).trans
      (nativeGroundRVEvaluation_class h00 linear hκ hs hc B hr hγ hΓ kind U)).symm
  refine he.trans ((nativeFullKeyDrop_value h00 linear hκ hs hr hγ hΓ kind
    (nativeVFZeroStratum A I) (nativeVFZeroPatternIndex I) ?_).trans ?_)
  · intro a i hi
    by_contra hn
    exact hi ((nativeVFZeroPatternIndex_range I i).mpr
      ((((nativeVFZeroStratum_mem A I a.val).mp a.property).2 i).mpr hn))
  · exact nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
      (GammaGroundBijection.ofCarrierEq (nativeFullKeyZeroStratum_image A I))

theorem nativeVFZeroStrata_raw_value_sum
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) :
    (∑ I : Finset (Fin n),nativeRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
      (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart
        (nativeVFZeroStratumRVObject hκ hs h00 hr A hpull hf I)))) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (nativeMixedFullKeyMap A).image := by
  rw [nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
    (nativeMixedFullKeyMap A).image
    (fun I => nativeRVZeroPatternBase (nativeMixedFullKeyMap A).image (Fin.castAdd r) I)
    (nativeRVZeroPatternBase_disjoint _ _) (nativeRVZeroPatternBase_cover _ _)]
  exact Finset.sum_congr rfl (fun I _ => nativeVFZeroStratumRVObject_raw_value h00 linear hκ hs hr hγ hΓ kind A hpull hf I)

end DiamondIntegral.Section5
