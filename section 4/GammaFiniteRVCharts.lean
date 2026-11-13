import «section 4».GammaFiniteBounds
import «section 4».RESFibreObjects
import «section 4».RVSharpProducts
import «section 4».RESChartRing

/-! Intrinsic finite Gamma objects and their actual RES sharp objects.
The sharp objects are full RV fibres, without chosen RV representatives. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaFiniteRVCharts
open GammaWeightedCharts FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure FiniteChart (B : Base (M := M)) (n : ℕ) extends Chart B n where
  finite_support : support.Finite

def ofTotal (B : Base (M := M)) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaOrderLogic.GammaDefinable B I) (hi : I.Finite)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : GammaDefinableMaps.MapDefinable B μ) :
    FiniteChart B n := ⟨GammaChartOperations.ofTotal B n I hI μ hμ, hi⟩

def product {B : Base (M := M)} {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) : FiniteChart B (n + m) :=
  ⟨GammaChartOperations.product a.toChart b.toChart, by
    have hf := (a.finite_support.prod b.finite_support).image
      (fun p : (Fin m → Values.Gamma (M := M)) × (Fin n → Values.Gamma (M := M)) => join n m p.1 p.2)
    apply hf.subset
    intro z hz
    exact ⟨(z ∘ headIndex n m, z ∘ tailIndex n m), ⟨hz.1, hz.2⟩, join_reconstruct n m z⟩⟩

def unit (B : Base (M := M)) : FiniteChart B 0 := ⟨GammaChartOperations.unit B, Set.toFinite _⟩

def sharp {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : RVMeasuredCharts.RESChart B n :=
  RESFibreObjects.sharpRESChart a.toChart a.finite_support

def bounded {B : Base (M := M)} {n : ℕ} (a : FiniteChart B n) : GammaBoundedRVCharts.BoundedChart B n :=
  GammaFiniteBounds.boundedChart a.toChart a.finite_support

def sharpProductIso {B : Base (M := M)} {n m : ℕ} (a : FiniteChart B m) (b : FiniteChart B n) :
    RVMeasuredCharts.Iso (sharp (product a b)).toChart
      (RVMeasuredProductProperties.resProduct (sharp a) (sharp b)).toChart :=
  RVSharpProducts.sharpProductIso a.toChart b.toChart

def sharpUnitIso (B : Base (M := M)) : RVMeasuredCharts.Iso (sharp (unit B)).toChart (RESChartRing.unit B).toChart :=
  RVSharpProducts.sharpUnitIso B

end DiamondIntegral.Section4.GammaFiniteRVCharts
