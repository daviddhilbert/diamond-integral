import «section 4».Section3RVRoundtripBridge
import «section 3».GammaGroundMeasuredRVProducts

/-! Actual Cartesian products commute with the two RV encodings. The
coordinate permutation is definable over the original base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVProductBridge
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def productIndices (n m : ℕ) : Fin (n + m) → Fin (n + m) :=
  join n m (Fin.natAdd n) (Fin.castAdd m)

theorem productIndices_surjective (n m : ℕ) : Function.Surjective (productIndices n m) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact ⟨tailIndex n m j, join_tail n m _ _ j⟩
  · exact ⟨headIndex n m j, join_head n m _ _ j⟩

theorem append_productIndices {n m : ℕ} (x : Fin n → CanonicalRV.RVSort M)
    (y : Fin m → CanonicalRV.RVSort M) :
    rvValues (rvAppend x y) ∘ productIndices n m = join n m (rvValues y) (rvValues x) := by
  apply FiniteTupleGraphProduct.block_ext n m
  · funext i
    change (rvAppend x y (productIndices n m (headIndex n m i))).val = _
    simp only [Function.comp_apply, productIndices, join_head]
    exact congrArg Subtype.val (Fin.append_right x y i)
  · funext i
    change (rvAppend x y (productIndices n m (tailIndex n m i))).val = _
    simp only [Function.comp_apply, productIndices, join_tail]
    exact congrArg Subtype.val (Fin.append_left x y i)

theorem rawDomain_product {n m : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (E : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (x : Fin (n + m) → M) :
    x ∈ rawDomain (gammaGroundRVProductDomain D E) ↔
      ∃ a : D, ∃ b : E, x = rvValues (rvAppend a.val b.val) := by
  constructor
  · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
    exact ⟨⟨t.val.1, t.property.1⟩, ⟨t.val.2, t.property.2⟩, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨rvAppend a.val b.val, ⟨⟨(a.val, b.val), a.property, b.property⟩, rfl⟩, rfl⟩

theorem product_bijOn {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    Set.BijOn (fun z => z ∘ productIndices U.arity V.arity)
      (Section3RVChartBridge.chart (U.product V)).domain
      (RVMeasuredProduct.product (Section3RVChartBridge.chart V) (Section3RVChartBridge.chart U)).domain := by
  refine ⟨?_, (productIndices_surjective U.arity V.arity).injective_comp_right.injOn, ?_⟩
  · intro z hz
    obtain ⟨a, b, rfl⟩ := (rawDomain_product U.domain V.domain z).mp hz
    change (rvValues (rvAppend a.val b.val) ∘ productIndices U.arity V.arity) ∈
      productSet (rawDomain V.domain) (rawDomain U.domain)
    rw [append_productIndices]
    exact (productSet_join _ _ _ _).mpr ⟨⟨b.val, b.property, rfl⟩, a.val, a.property, rfl⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := (productSet_exists _ _ z).mp hz
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨rvValues (rvAppend a b), (rawDomain_product U.domain V.domain _).mpr
      ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩, append_productIndices a b⟩

def productIso {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    RVForgetScissors.UnderlyingIso (Section3RVChartBridge.chart (U.product V))
      (RVMeasuredProduct.product (Section3RVChartBridge.chart V) (Section3RVChartBridge.chart U)) :=
  RVForgetScissors.ofMap _ _ (fun z => z ∘ productIndices U.arity V.arity)
    (RVCoordinateMaps.coordinate_graph_definable B _ (rawDomain_definable _) _) (product_bijOn U V)

theorem unpack_append {n m : ℕ} (D : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (E : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (a : D) (b : E) :
    gammaGroundRVUnpack D E ⟨rvAppend a.val b.val,
      ⟨⟨(a.val, b.val), a.property, b.property⟩, rfl⟩⟩ = ⟨(a.val, b.val), a.property, b.property⟩ :=
  (gammaGroundRVPack D E).toImage.inverse_apply
    ((gammaGroundRVPack D E).toImage_bijective (gammaGroundRVPack_injective D E))
    ⟨(a.val, b.val), a.property, b.property⟩

def measuredProductIso {k l : ℕ} (U : GammaGroundMeasuredRVObject hc B k)
    (V : GammaGroundMeasuredRVObject hc B l) :
    Iso (Section3MeasuredRVChartBridge.chart (U.product V))
      (RVMeasuredProduct.product (Section3MeasuredRVChartBridge.chart V) (Section3MeasuredRVChartBridge.chart U)) where
  equiv := (productIso U.underlying V.underlying).equiv
  graph_definable := (productIso U.underlying V.underlying).graph_definable
  weight_eq z := by
    obtain ⟨a, b, hz⟩ := (rawDomain_product U.underlying.domain V.underlying.domain z.val).mp z.property
    let p : (U.product V).underlying.domain := ⟨rvAppend a.val b.val,
      ⟨⟨(a.val, b.val), a.property, b.property⟩, rfl⟩⟩
    change (Section3MeasuredRVChartBridge.chart (U.product V)).correctedWeight z.val =
      (RVMeasuredProduct.product (Section3MeasuredRVChartBridge.chart V)
        (Section3MeasuredRVChartBridge.chart U)).correctedWeight
        (z.val ∘ productIndices U.underlying.arity V.underlying.arity)
    rw [hz, append_productIndices]
    have hw := RVMeasuredProductProperties.product_weight_join
      (Section3MeasuredRVChartBridge.chart V) (Section3MeasuredRVChartBridge.chart U)
      (rvValues b.val) (rvValues a.val)
    change (RVMeasuredProduct.product (Section3MeasuredRVChartBridge.chart V)
      (Section3MeasuredRVChartBridge.chart U)).correctedWeight
      (join U.underlying.arity V.underlying.arity (rvValues b.val) (rvValues a.val)) = _ at hw
    rw [hw]
    have hU := Section3MeasuredRVChartBridge.chart_weight U a
    have hV := Section3MeasuredRVChartBridge.chart_weight V b
    have hP := Section3MeasuredRVChartBridge.chart_weight (U.product V) p
    change (Section3MeasuredRVChartBridge.chart (U.product V)).correctedWeight
      (rvValues (rvAppend a.val b.val)) = (U.product V).combinedWeight p at hP
    rw [hP, hV, hU, GammaGroundMeasuredRVObject.product_combined]
    have hp := unpack_append U.underlying.domain V.underlying.domain a b
    change gammaGroundRVUnpack U.underlying.domain V.underlying.domain p = _ at hp
    change U.combinedWeight ⟨(gammaGroundRVUnpack _ _ p).val.1, _⟩ *
      V.combinedWeight ⟨(gammaGroundRVUnpack _ _ p).val.2, _⟩ = _
    simp only [hp]
    exact mul_comm _ _

end DiamondIntegral.Section4.Section3RVProductBridge
