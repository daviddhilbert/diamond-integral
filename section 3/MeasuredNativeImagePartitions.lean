import «section 3».MeasuredNativeTensorCharts
import «section 3».GammaGroundMeasuredRVFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundMeasuredNativeTensorChart.nativeForm (Z : GammaGroundMeasuredNativeTensorChart hc B k) :
    GammaGroundVolumeForm hc B Z.underlying.source := Z.object.combinedWeightForm.comp Z.bijection.map

theorem GammaGroundMeasuredNativeTensorChart.nativeForm_value (Z : GammaGroundMeasuredNativeTensorChart hc B k)
    (z : Z.underlying.source) : gammaGroundFormValue Z.nativeForm z = Z.weight (rvUnitTupleValues z.val.1) :=
  (Z.object.combinedWeightForm_value (Z.bijection.map z)).trans (Z.native_weight z)

theorem GammaGroundMeasuredRVObject.restrict_weight (U : GammaGroundMeasuredRVObject hc B k)
    (X : GammaGroundDefSet hc B (rawRVSpace U.underlying.arity)) (hX : X.carrier ⊆ U.underlying.domain.carrier)
    (a : (U.restrict X hX).underlying.domain) :
    (U.restrict X hX).combinedWeight a = U.combinedWeight ⟨a.val,hX a.property⟩ := rfl

theorem gammaGroundMeasuredNativeTensorChart_restrict_image_class
    (Z : GammaGroundMeasuredNativeTensorChart hc B k) (U : GammaGroundMeasuredRVObject hc B k)
    (f : GammaGroundMap Z.underlying.source U.underlying.domain) (hf : Function.Injective f)
    (hw : ∀ z, U.combinedWeight (f z) = Z.weight (rvUnitTupleValues z.val.1)) :
    gammaGroundMeasuredRVSemiringClass (U.restrict f.image f.image_subset_target) = gammaGroundMeasuredTensorMap Z.value := by
  let e : GammaGroundBijection Z.underlying.source f.image := ⟨f.toImage,f.toImage_bijective hf⟩
  let F : GammaGroundBijection Z.object.underlying.domain (U.restrict f.image f.image_subset_target).underlying.domain :=
    e.comp Z.bijection.symm
  have hF : ∀ a : Z.object.underlying.domain, Z.object.combinedWeight a =
      (U.restrict f.image f.image_subset_target).combinedWeight (F.map a) := by
    intro a
    obtain ⟨z,rfl⟩ := Z.bijection.bijective.2 a
    have he : F.map (Z.bijection.map z) = f.toImage z := by
      exact congrArg e.map (Z.bijection.map.inverse_apply Z.bijection.bijective z)
    have heAmbient : GammaGroundMap.inclusion f.image_subset_target (F.map (Z.bijection.map z)) = f z := by
      apply Subtype.ext
      exact congrArg (fun p : f.image => p.val) he
    have ht : (U.restrict f.image f.image_subset_target).combinedWeight (F.map (Z.bijection.map z)) =
        U.combinedWeight (f z) :=
      (U.restrict_weight f.image f.image_subset_target (F.map (Z.bijection.map z))).trans (congrArg U.combinedWeight heAmbient)
    exact (Z.native_weight z).trans ((hw z).symm.trans ht.symm)
  let h : GammaGroundMeasuredRVHom Z.object (U.restrict f.image f.image_subset_target) := ⟨F,hF⟩
  exact (gammaGroundMeasuredRVSemiringClass_iso (asIso (show _ ⟶ _ from h))).symm.trans Z.value_image.symm

/-- A measured native image partition presents exactly the inherited
positive RV object and its weights, including residual comparisons. -/
theorem gammaGroundMeasuredNativeTensorCharts_RV_image_partition {ι : Type} [Fintype ι]
    (U : GammaGroundMeasuredRVObject hc B k) (Z : ι → GammaGroundMeasuredNativeTensorChart hc B k)
    (f : ∀ i, GammaGroundMap (Z i).underlying.source U.underlying.domain)
    (hf : ∀ i, Function.Injective (f i))
    (hw : ∀ i z, U.combinedWeight (f i z) = (Z i).weight (rvUnitTupleValues z.val.1))
    (hd : ∀ i j, i ≠ j → Disjoint (f i).image.carrier (f j).image.carrier)
    (hcov : ∀ x, x ∈ U.underlying.domain.carrier ↔ ∃ i, x ∈ (f i).image.carrier) :
    gammaGroundMeasuredRVSemiringClass U = gammaGroundMeasuredTensorMap (∑ i, (Z i).value) := by
  calc
    _ = ∑ i, gammaGroundMeasuredRVSemiringClass
        (U.restrict (f i).image (fun x hx => (hcov x).mpr ⟨i,hx⟩)) :=
      gammaGroundMeasuredRVSemiringClass_finite_partition U (fun i => (f i).image) hd hcov
    _ = ∑ i, gammaGroundMeasuredTensorMap (Z i).value := by
      apply Finset.sum_congr rfl
      intro i _
      exact gammaGroundMeasuredNativeTensorChart_restrict_image_class (Z i) U (f i) (hf i) (hw i)
    _ = _ := (map_sum gammaGroundMeasuredTensorMap (fun i => (Z i).value) Finset.univ).symm
end DiamondIntegral.Section3
