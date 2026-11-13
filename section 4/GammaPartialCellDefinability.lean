import «section 4».GammaWeightedCharts
import «section 4».GammaCellUnboundedSections
import «section 4».GammaMapOrder

/-! Original-base definability of cylindrical shapes with partial endpoint
functions. An endpoint graph over its actual domain is extended only by
the identity value outside that domain. No definable RV representatives
or cell-decomposition existence theorem is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPartialCellDefinability
open GammaOrderLogic GammaDefinableMaps GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def extend {B : Base (M := M)} {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B (graphCell C T)) : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) :=
  (⟨C, hC, T, hT⟩ : GammaWeightedCharts.Chart B n).normalizedVolume

theorem extend_definable {B : Base (M := M)} {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B (graphCell C T)) : MapDefinable B (extend C hC T hT) :=
  (⟨C, hC, T, hT⟩ : GammaWeightedCharts.Chart B n).normalizedVolume_definable

theorem extend_on {B : Base (M := M)} {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B (graphCell C T)) (y : Fin n → Values.Gamma (M := M)) (hy : y ∈ C) :
    extend C hC T hT y = T y := (⟨C, hC, T, hT⟩ : GammaWeightedCharts.Chart B n).normalizedVolume_on y hy

theorem graph_restrict (B : Base (M := M)) {n : ℕ} (C D : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (hCD : C ⊆ D)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B (graphCell D T)) : GammaDefinable B (graphCell C T) := by
  have h := GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.preimage_definable_base B C hC Fin.succ) hT
  convert h using 1
  ext z
  change (Fin.tail z ∈ C ∧ z 0 = T (Fin.tail z)) ↔
    (Fin.tail z ∈ C ∧ Fin.tail z ∈ D ∧ z 0 = T (Fin.tail z))
  exact ⟨fun hz => ⟨hz.1, hCD hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩

theorem graph_definable (B : Base (M := M)) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) : GammaDefinable B (graphCell C T) :=
  GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.preimage_definable_base B C hC Fin.succ) hT

theorem upperRay_definable (B : Base (M := M)) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hl : MapDefinable B l) : GammaDefinable B (upperRayCell C l) :=
  GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.preimage_definable_base B C hC Fin.succ)
    (GammaMapOrder.lt_maps_definable B _ _ (reindex_definable B l hl Fin.succ) (projection_definable B 0))

theorem lowerRay_definable (B : Base (M := M)) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : MapDefinable B u) : GammaDefinable B (lowerRayCell C u) :=
  GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.preimage_definable_base B C hC Fin.succ)
    (GammaMapOrder.lt_maps_definable B _ _ (projection_definable B 0) (reindex_definable B u hu Fin.succ))

theorem band_definable (B : Base (M := M)) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hl : MapDefinable B l) (hu : MapDefinable B u) : GammaDefinable B (bandCell C l u) :=
  GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.preimage_definable_base B C hC Fin.succ)
    (GammaRelationLogic.inter_definable_base B _ _
      (GammaMapOrder.lt_maps_definable B _ _ (reindex_definable B l hl Fin.succ) (projection_definable B 0))
      (GammaMapOrder.lt_maps_definable B _ _ (projection_definable B 0) (reindex_definable B u hu Fin.succ)))

theorem line_definable (B : Base (M := M)) {n : ℕ} (C : Set (Fin n → Values.Gamma (M := M)))
    (hC : GammaDefinable B C) : GammaDefinable B (lineCell C) :=
  GammaRelationLogic.preimage_definable_base B C hC Fin.succ

end DiamondIntegral.Section4.GammaPartialCellDefinability
