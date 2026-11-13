import «section 4».GammaBoundedProducts
import «section 4».RVSharpProducts
import «section 4».RVBoundedCharts
import «section 4».RVBoundedRing

/-! Bounded Gamma charts and their actual bounded RV sharp objects.
The parameter base and the original partial volume forms are retained. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedRVCharts
open GammaWeightedCharts GammaOrderLogic GammaDefinableMaps GammaBoundedProducts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure BoundedChart (B : Base (M := M)) (n : ℕ) extends Chart B n where
  domain_bounded : DomainBounded support

def ofTotal (B : Base (M := M)) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hb : DomainBounded I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : BoundedChart B n :=
  ⟨GammaChartOperations.ofTotal B n I hI μ hμ, hb⟩

def product {B : Base (M := M)} {n m : ℕ} (a : BoundedChart B m) (b : BoundedChart B n) :
    BoundedChart B (n + m) :=
  ⟨GammaChartOperations.product a.toChart b.toChart, a.domain_bounded.product b.domain_bounded⟩

def unit (B : Base (M := M)) : BoundedChart B 0 :=
  ⟨GammaChartOperations.unit B, DomainBounded.unit⟩

def sharp {B : Base (M := M)} {n : ℕ} (a : BoundedChart B n) : RVBoundedCharts.BoundedChart B n :=
  ⟨RVSharpCharts.sharpChart a.toChart, RVMeasuredBounds.sharp_domain_bounded a.toChart a.domain_bounded⟩

def sharpProductIso {B : Base (M := M)} {n m : ℕ} (a : BoundedChart B m) (b : BoundedChart B n) :
    RVMeasuredCharts.Iso (sharp (product a b)).toChart
      (RVBoundedCharts.product (sharp a) (sharp b)).toChart :=
  RVSharpProducts.sharpProductIso a.toChart b.toChart

def sharpUnitIso (B : Base (M := M)) :
    RVMeasuredCharts.Iso (sharp (unit B)).toChart (RVBoundedRing.unit B).toChart :=
  RVSharpProducts.sharpUnitIso B

end DiamondIntegral.Section4.GammaBoundedRVCharts
