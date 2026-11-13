import «section 3».MeasuredNativeBoxResidualPartitions
import «section 3».MeasuredTensorRankLayerAtlas
import «section 3».RankLayerResidualAtlas
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
variable {ι : Type} [Fintype ι]
namespace GammaGroundMeasuredTensorResidual
variable (L : GammaGroundMeasuredTensorRankLayer hc B k m)
variable (E : GammaGroundTensorRankLayerMatchedFamily L.unmeasured ι)

def weight (c : E.ResidualIndex) :
    (Fin (E.residualChart c).gammaDegree → Values.Gamma (M := M)) → Values.Gamma (M := M) := by
  rcases c with ⟨j,c⟩ | j
  · exact L.weight j
  · exact L.lower_weight j

theorem weight_definable (c : E.ResidualIndex) :
    FullGammaFunction (integrationGammaBase B) (weight L E c) := by
  rcases c with ⟨j,c⟩ | j
  · exact L.weight_definable j
  · exact L.lower_weight_definable j

def chart (c : E.ResidualIndex) : GammaGroundMeasuredNativeTensorChart hc B k :=
  ⟨E.residualChart c,weight L E c,weight_definable L E c⟩

def object : GammaGroundMeasuredRVObject hc B k :=
  L.object.restrict (L.object.underlying.domain.sdiff E.union) (fun _ h => h.1)

theorem map_weight (c : E.ResidualIndex) (z : (chart L E c).underlying.source) :
    (object L E).combinedWeight (E.residualMap c z) =
      (chart L E c).weight (rvUnitTupleValues z.val.1) := by
  have h := L.object.restrict_weight (L.object.underlying.domain.sdiff E.union) (fun _ h => h.1)
    (E.residualMap c z)
  refine h.trans ?_
  rcases c with ⟨j,c⟩ | j
  · exact L.topMap_weight j ((E.remainderBox ⟨j,c⟩).inclusion z)
  · exact L.lowerMap_weight j z

/-- The weighted residual charts present the actual inherited measured
RV complement using precisely the original underlying atlas. -/
theorem value_image :
    gammaGroundMeasuredTensorMap (∑ c : E.ResidualIndex, (chart L E c).value) =
      gammaGroundMeasuredRVSemiringClass (object L E) := by
  symm
  apply gammaGroundMeasuredNativeTensorCharts_RV_image_partition (object L E) (chart L E) E.residualMap
    E.residualMap_injective (map_weight L E) E.residualMap_disjoint
  intro z
  constructor
  · intro hz
    obtain ⟨c,u,hu⟩ := E.residualMap_cover ⟨z,hz⟩
    exact ⟨c,u,congrArg (fun v : E.residualObject.domain => v.val) hu⟩
  · rintro ⟨c,u,hu⟩
    exact hu ▸ (E.residualMap c u).property

/-- This decomposition is an equality in the positive tensor semiring:
all matched boxes and all inherited residual weights remain present. -/
theorem value_split :
    L.value = (∑ i : ι, (E.box i).measuredValue (L.weight (E.parent i)) (L.weight_definable (E.parent i))) +
      ∑ c : E.ResidualIndex, (chart L E c).value := by
  have hr : (∑ c : E.ResidualIndex, (chart L E c).value) =
      (∑ j : Fin L.topCount, ∑ c : GammaGroundTensorParentRemainderIndex L.residue L.gamma E.parent E.box j,
        (gammaGroundTensorParentRemainderBox L.residue L.gamma E.parent E.box j c).measuredValue (L.weight j) (L.weight_definable j)) +
          ∑ j : Fin L.lower.length, (L.lowerChart j).value := by
    calc
      _ = (∑ c : E.TopResidualIndex, (E.remainderBox c).measuredValue (L.weight c.1) (L.weight_definable c.1)) +
          ∑ j : Fin L.lower.length, (L.lowerChart j).value := Fintype.sum_sum_type (fun c : E.ResidualIndex => (chart L E c).value)
      _ = _ := congrArg (fun v => v + ∑ j : Fin L.lower.length, (L.lowerChart j).value)
        (Fintype.sum_sigma' (fun j c => (gammaGroundTensorParentRemainderBox L.residue L.gamma E.parent E.box j c).measuredValue (L.weight j) (L.weight_definable j)))
  rw [hr]
  change (∑ j, L.topValue j) + (∑ j, (L.lowerChart j).value) = _
  have h := gammaGroundMeasuredTensorParents_residual_value_split L.residue L.gamma L.unmeasured.topMap
    L.weight L.weight_definable E.parent E.box E.disjoint
  change (∑ j, L.topValue j) = _ at h
  rw [h]
  exact add_assoc _ _ _
end GammaGroundMeasuredTensorResidual
end DiamondIntegral.Section3
