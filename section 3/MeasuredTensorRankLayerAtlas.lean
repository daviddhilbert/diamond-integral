import «section 3».MeasuredTensorRankLayerNormalForm
import «section 3».TensorRankLayerAtlas
import «section 3».GammaGroundWeightGluing
import «section 3».MeasuredNativeImagePartitions
import «section 3».GammaGroundMeasuredRVGradingConsequences
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k m : ℕ}
namespace GammaGroundMeasuredTensorRankLayer

abbrev Index (L : GammaGroundMeasuredTensorRankLayer hc B k m) := Sum (Fin L.topCount) (Fin L.lower.length)

def chart (L : GammaGroundMeasuredTensorRankLayer hc B k m) : L.Index → GammaGroundMeasuredNativeTensorChart hc B k :=
  Sum.elim L.topChart L.lowerChart

def map (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : L.Index) :
    GammaGroundMap (L.chart i).underlying.source L.unmeasured.object.domain := by
  rcases i with i | j
  · exact L.unmeasured.topMap i
  · exact L.unmeasured.lowerMap j

theorem map_injective (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : L.Index) : Function.Injective (L.map i) := by
  rcases i with i | j
  · exact L.unmeasured.topMap_injective i
  · exact L.unmeasured.lowerMap_injective j

theorem map_disjoint (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i j : L.Index) (hij : i ≠ j) :
    Disjoint (L.map i).image.carrier (L.map j).image.carrier := by
  rcases i with i | i <;> rcases j with j | j
  · exact L.unmeasured.topMap_disjoint i j (fun he => hij (congrArg Sum.inl he))
  · exact L.unmeasured.top_lower_disjoint i j
  · exact (L.unmeasured.top_lower_disjoint j i).symm
  · exact L.unmeasured.lowerMap_disjoint i j (fun he => hij (congrArg Sum.inr he))

theorem map_cover (L : GammaGroundMeasuredTensorRankLayer hc B k m) (x : L.unmeasured.object.domain) :
    ∃ i : L.Index, ∃ z, L.map i z = x := by
  rcases L.unmeasured.cover x with ⟨i,z,hz⟩ | ⟨j,z,hz⟩
  · exact ⟨.inl i,z,hz⟩
  · exact ⟨.inr j,z,hz⟩

theorem weightForm_exists (L : GammaGroundMeasuredTensorRankLayer hc B k m) :
    ∃ W : GammaGroundVolumeForm hc B L.unmeasured.object.domain,
      ∀ i z, (W (L.map i z)).val = ((L.chart i).nativeForm z).val :=
  gammaGroundVolumeForm_glue_injective_charts L.map L.map_injective L.map_disjoint L.map_cover (fun i => (L.chart i).nativeForm)

def weightForm (L : GammaGroundMeasuredTensorRankLayer hc B k m) : GammaGroundVolumeForm hc B L.unmeasured.object.domain :=
  Classical.choose L.weightForm_exists

theorem weightForm_map (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : L.Index) (z : (L.chart i).underlying.source) :
    (L.weightForm (L.map i z)).val = ((L.chart i).nativeForm z).val := Classical.choose_spec L.weightForm_exists i z

/-- Prescribing the glued combined weight retains literally the old
rank-layer RV object and its actual native coordinate atlas. -/
def object (L : GammaGroundMeasuredTensorRankLayer hc B k m) : GammaGroundMeasuredRVObject hc B k :=
  L.unmeasured.object.withCombinedWeight L.weightForm

theorem map_weight (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : L.Index) (z : (L.chart i).underlying.source) :
    L.object.combinedWeight (L.map i z) = (L.chart i).weight (rvUnitTupleValues z.val.1) := by
  change (L.unmeasured.object.withCombinedWeight L.weightForm).combinedWeight (L.map i z) = _
  rw [GammaGroundRVObject.withCombinedWeight_value]
  exact (L.weightForm_map i z).trans ((L.chart i).nativeForm_value z)

theorem topMap_weight (L : GammaGroundMeasuredTensorRankLayer hc B k m) (i : Fin L.topCount)
    (z : gammaGroundNativeProductDomain (L.residue i) (L.gamma i)) :
    L.object.combinedWeight (L.unmeasured.topMap i z) = L.weight i (rvUnitTupleValues z.val.1) :=
  L.map_weight (.inl i) z

theorem lowerMap_weight (L : GammaGroundMeasuredTensorRankLayer hc B k m) (j : Fin L.lower.length)
    (z : (L.lower.get j).source) :
    L.object.combinedWeight (L.unmeasured.lowerMap j z) = L.lower_weight j (rvUnitTupleValues z.val.1) :=
  L.map_weight (.inr j) z

theorem value_charts (L : GammaGroundMeasuredTensorRankLayer hc B k m) :
    L.value = ∑ i : L.Index, (L.chart i).value := by
  calc
    _ = (∑ i, (L.topChart i).value) + ∑ j, (L.lowerChart j).value := by simp only [value,topChart_value]
    _ = _ := (Fintype.sum_sum_type (fun i : L.Index => (L.chart i).value)).symm

theorem value_image (L : GammaGroundMeasuredTensorRankLayer hc B k m) :
    gammaGroundMeasuredTensorMap L.value = gammaGroundMeasuredRVSemiringClass L.object := by
  rw [L.value_charts]
  symm
  apply gammaGroundMeasuredNativeTensorCharts_RV_image_partition L.object L.chart L.map
    L.map_injective L.map_weight L.map_disjoint
  intro x
  constructor
  · intro hx
    obtain ⟨i,z,hz⟩ := L.map_cover ⟨x,hx⟩
    exact ⟨i,z,congrArg (fun y : L.unmeasured.object.domain => y.val) hz⟩
  · rintro ⟨i,z,hz⟩
    exact hz ▸ (L.map i z).property

theorem iso_of_equal_images (L R : GammaGroundMeasuredTensorRankLayer hc B k m)
    (h : gammaGroundMeasuredTensorMap L.value = gammaGroundMeasuredTensorMap R.value) : Nonempty (L.object ≅ R.object) := by
  apply gammaGroundMeasuredRVClass_eq_iff_iso.mp
  apply gammaGroundMeasuredRVKPlusToSemiring_injective
  rw [gammaGroundMeasuredRVKPlusToSemiring_class,gammaGroundMeasuredRVKPlusToSemiring_class]
  rw [← L.value_image,← R.value_image]
  exact h
end GammaGroundMeasuredTensorRankLayer
end DiamondIntegral.Section3
