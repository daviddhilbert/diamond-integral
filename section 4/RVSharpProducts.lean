import «section 4».RVCoordinateMaps
import «section 4».RVMeasuredProductProperties
import «section 4».RVSharpCharts
import «section 4».GammaChartOperations
import «section 4».RVChartRing

/-! Taking the full proper RV preimage of a Gamma chart preserves actual
products and the unit up to original-base measured RV isomorphism. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVSharpProducts
open RVMeasuredCharts RVSharpCharts GammaRVChartPresentation FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem sharp_product_domain {B : Base (M := M)} {n m : ℕ}
    (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n) :
    (sharpChart (GammaChartOperations.product a b)).domain =
      (RVMeasuredProduct.product (sharpChart a) (sharpChart b)).domain := by
  ext u
  change (Proper u ∧ (codeValues u ∘ headIndex n m ∈ a.support ∧
      codeValues u ∘ tailIndex n m ∈ b.support)) ↔
    ((Proper (u ∘ headIndex n m) ∧ codeValues (u ∘ headIndex n m) ∈ a.support) ∧
      (Proper (u ∘ tailIndex n m) ∧ codeValues (u ∘ tailIndex n m) ∈ b.support))
  constructor
  · intro h
    exact ⟨⟨fun i => h.1 (headIndex n m i), h.2.1⟩,
      ⟨fun i => h.1 (tailIndex n m i), h.2.2⟩⟩
  · intro h
    exact ⟨GammaBoundedProducts.all_coordinates n m NonzeroRV u h.1.1 h.2.1, h.1.2, h.2.2⟩

theorem sharp_product_weight {B : Base (M := M)} {n m : ℕ}
    (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n)
    (u : Fin (n + m) → M) (hu : u ∈ (sharpChart (GammaChartOperations.product a b)).domain) :
    (sharpChart (GammaChartOperations.product a b)).correctedWeight u =
      (RVMeasuredProduct.product (sharpChart a) (sharpChart b)).correctedWeight u := by
  have hv : (sharpChart (GammaChartOperations.product a b)).volume u =
      (RVMeasuredProduct.product (sharpChart a) (sharpChart b)).volume u := by
    change a.normalizedVolume (codeValues u ∘ headIndex n m) *
        b.normalizedVolume (codeValues u ∘ tailIndex n m) =
      a.volume (codeValues u ∘ headIndex n m) * b.volume (codeValues u ∘ tailIndex n m)
    rw [a.normalizedVolume_on _ hu.2.1, b.normalizedVolume_on _ hu.2.2]
  have hc : (RVMeasuredProduct.product (sharpChart a) (sharpChart b)).coordinate u = u :=
    join_reconstruct n m u
  change (sharpChart (GammaChartOperations.product a b)).volume u * (∏ i, codeValue (u i)) =
    (RVMeasuredProduct.product (sharpChart a) (sharpChart b)).volume u *
      (∏ i, codeValue ((RVMeasuredProduct.product (sharpChart a) (sharpChart b)).coordinate u i))
  rw [hv, hc]

def sharpProductIso {B : Base (M := M)} {n m : ℕ}
    (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n) :
    Iso (sharpChart (GammaChartOperations.product a b))
      (RVMeasuredProduct.product (sharpChart a) (sharpChart b)) :=
  RVCoordinateMaps.coordinateIso _ _ id
    ⟨(by intro u hu; exact (sharp_product_domain a b) ▸ hu),
      (by intro x hx y hy h; exact h),
      (by intro u hu; exact ⟨u, (sharp_product_domain a b).symm ▸ hu, rfl⟩)⟩
    (sharp_product_weight a b)

theorem sharp_product_class {B : Base (M := M)} {n m : ℕ}
    (a : GammaWeightedCharts.Chart B m) (b : GammaWeightedCharts.Chart B n) :
    RVChartRing.objectClass (sharpChart (GammaChartOperations.product a b)) =
      RVChartRing.objectClass (sharpChart a) * RVChartRing.objectClass (sharpChart b) :=
  (RVChartRing.objectClass_iso (sharpProductIso a b)).trans (RVChartRing.objectClass_product _ _)

def sharpUnitIso (B : Base (M := M)) :
    Iso (sharpChart (GammaChartOperations.unit B)) (RVChartRing.unit B) :=
  RVCoordinateMaps.coordinateIso _ _ id
    ⟨(by intro u hu; exact Set.mem_univ _),
      (by intro x hx y hy h; exact h),
      (by intro u hu; exact ⟨u, ⟨fun i => i.elim0, Set.mem_univ _⟩, rfl⟩)⟩
    (by intro u hu; simp [Chart.correctedWeight, sharpChart, GammaChartOperations.unit,
      GammaChartOperations.ofTotal, RVChartRing.unit, RVMeasuredCharts.weightedUnit])

theorem sharp_unit_class (B : Base (M := M)) :
    RVChartRing.objectClass (sharpChart (GammaChartOperations.unit B)) = 1 :=
  (RVChartRing.objectClass_iso (sharpUnitIso B)).trans (RVChartRing.objectClass_unit B)

end DiamondIntegral.Section4.RVSharpProducts
