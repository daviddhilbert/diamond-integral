import «section 3».TensorRankLayerNormalForm
import «section 3».NativeTensorListSubindices
import «section 3».TensorLocalMatches
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
namespace GammaGroundTensorRankLayer

def object (L : GammaGroundTensorRankLayer hc B k m) := gammaGroundNativeTensorListObject L.charts

def topIndex (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) : Fin L.charts.length :=
  gammaGroundNativeTensorListPrefixIndex (List.ofFn L.topChart) L.lower (gammaGroundNativeTensorOfFnIndex L.topChart i)

def lowerIndex (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.lower.length) : Fin L.charts.length :=
  gammaGroundNativeTensorListSuffixIndex (List.ofFn L.topChart) L.lower i

theorem top_get (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) : L.charts.get (L.topIndex i) = L.topChart i :=
  (gammaGroundNativeTensorListPrefix_get _ _ _).trans (gammaGroundNativeTensorOfFn_get L.topChart i)

theorem lower_get (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.lower.length) : L.charts.get (L.lowerIndex i) = L.lower.get i :=
  gammaGroundNativeTensorListSuffix_get _ _ i

def topMap (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) :
    GammaGroundMap (gammaGroundNativeProductDomain (L.residue i) (L.gamma i)) L.object.domain :=
  gammaGroundNativeTensorListInjectionOfEq L.charts (L.topIndex i) (L.topChart i) (L.top_get i)

def lowerMap (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.lower.length) :
    GammaGroundMap (L.lower.get i).source L.object.domain :=
  gammaGroundNativeTensorListInjectionOfEq L.charts (L.lowerIndex i) (L.lower.get i) (L.lower_get i)

theorem topMap_image (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) :
    (L.topMap i).image.carrier = (gammaGroundNativeTensorListInjection L.charts (L.topIndex i)).image.carrier :=
  gammaGroundNativeTensorListInjectionOfEq_image _ _ _ _

theorem lowerMap_image (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.lower.length) :
    (L.lowerMap i).image.carrier = (gammaGroundNativeTensorListInjection L.charts (L.lowerIndex i)).image.carrier :=
  gammaGroundNativeTensorListInjectionOfEq_image _ _ _ _

theorem topMap_injective (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) : Function.Injective (L.topMap i) :=
  gammaGroundNativeTensorListInjectionOfEq_injective _ _ _ _

theorem lowerMap_injective (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.lower.length) : Function.Injective (L.lowerMap i) :=
  gammaGroundNativeTensorListInjectionOfEq_injective _ _ _ _

theorem lower_rank_at (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.lower.length) :
    (L.lower.get i).gammaDegree < m := (List.forall_mem_iff_get.mp L.lower_rank) i

theorem topMap_disjoint (L : GammaGroundTensorRankLayer hc B k m) (i j : Fin L.topCount) (hij : i ≠ j) :
    Disjoint (L.topMap i).image.carrier (L.topMap j).image.carrier := by
  rw [L.topMap_image,L.topMap_image]
  apply gammaGroundNativeTensorListInjection_disjoint
  intro he
  apply hij
  apply Fin.ext
  exact congrArg (fun z : Fin L.charts.length => z.val) he

theorem lowerMap_disjoint (L : GammaGroundTensorRankLayer hc B k m) (i j : Fin L.lower.length) (hij : i ≠ j) :
    Disjoint (L.lowerMap i).image.carrier (L.lowerMap j).image.carrier := by
  rw [L.lowerMap_image,L.lowerMap_image]
  apply gammaGroundNativeTensorListInjection_disjoint
  intro he
  have hv := congrArg (fun z : Fin L.charts.length => z.val) he
  change (List.ofFn L.topChart).length+i.val = (List.ofFn L.topChart).length+j.val at hv
  exact hij (Fin.ext (Nat.add_left_cancel hv))

theorem top_lower_disjoint (L : GammaGroundTensorRankLayer hc B k m) (i : Fin L.topCount) (j : Fin L.lower.length) :
    Disjoint (L.topMap i).image.carrier (L.lowerMap j).image.carrier := by
  rw [L.topMap_image,L.lowerMap_image]
  apply gammaGroundNativeTensorListInjection_disjoint
  intro he
  have hv := congrArg (fun z : Fin L.charts.length => z.val) he
  change i.val = (List.ofFn L.topChart).length+j.val at hv
  rw [List.length_ofFn] at hv
  have hi := i.isLt
  omega

/-- The maximal-rank charts and the old lower-rank charts cover the
actual RV object by their original injective product presentations. -/
theorem cover (L : GammaGroundTensorRankLayer hc B k m) (v : L.object.domain) :
    (∃ i : Fin L.topCount, ∃ u : gammaGroundNativeProductDomain (L.residue i) (L.gamma i), L.topMap i u = v) ∨
      ∃ j : Fin L.lower.length, ∃ u : (L.lower.get j).source, L.lowerMap j u = v := by
  obtain ⟨j,u,hu⟩ := gammaGroundNativeTensorListInjection_cover L.charts v
  have hmem : v.val ∈ (gammaGroundNativeTensorListInjection L.charts j).image.carrier :=
    ⟨u,congrArg (fun z : L.object.domain => z.val) hu⟩
  by_cases hj : j.val < L.topCount
  · let i : Fin L.topCount := ⟨j.val,hj⟩
    have he : L.topIndex i = j := Fin.ext rfl
    have hm : v.val ∈ (L.topMap i).image.carrier := by
      rw [L.topMap_image,he]
      exact hmem
    obtain ⟨u',hu'⟩ := hm
    exact Or.inl ⟨i,u',Subtype.ext hu'⟩
  · have hjbound : j.val < L.topCount+L.lower.length := by
      simpa only [charts,List.length_append,List.length_ofFn] using j.isLt
    let i : Fin L.lower.length := ⟨j.val-L.topCount,by omega⟩
    have he : L.lowerIndex i = j := by
      apply Fin.ext
      change (List.ofFn L.topChart).length+(j.val-L.topCount) = j.val
      rw [List.length_ofFn]
      omega
    have hm : v.val ∈ (L.lowerMap i).image.carrier := by
      rw [L.lowerMap_image,he]
      exact hmem
    obtain ⟨u',hu'⟩ := hm
    exact Or.inr ⟨i,u',Subtype.ext hu'⟩

theorem value_image (L : GammaGroundTensorRankLayer hc B k m) :
    gammaGroundUnmeasuredTensorMap L.value = gammaGroundRVSemiringClass L.object := by
  rw [L.value_charts]
  exact gammaGroundNativeTensorListObject_image L.charts

theorem iso_of_equal_images (L R : GammaGroundTensorRankLayer hc B k m)
    (h : gammaGroundUnmeasuredTensorMap L.value = gammaGroundUnmeasuredTensorMap R.value) : Nonempty (L.object ≅ R.object) := by
  apply gammaGroundNativeTensorListObject_iso_of_equal_images L.charts R.charts
  rw [← L.value_charts,← R.value_charts]
  exact h
end GammaGroundTensorRankLayer
end DiamondIntegral.Section3
