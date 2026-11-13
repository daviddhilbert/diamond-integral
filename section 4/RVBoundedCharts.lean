import «section 4».RVMeasuredProductProperties

/-! Actual doubly bounded measured RV objects, with products, the unit
and the inclusion of all measured RES objects. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBoundedCharts
open RVMeasuredCharts RVMeasuredBounds
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure BoundedChart (B : Base (M := M)) (k : ℕ) extends Chart B k where
  domain_bounded : DomainBounded toChart

def product {B : Base (M := M)} {k l : ℕ} (a : BoundedChart B k) (b : BoundedChart B l) :
    BoundedChart B (l + k) :=
  ⟨RVMeasuredProduct.product a.toChart b.toChart,
    RVMeasuredProductProperties.product_domain_bounded a.toChart b.toChart a.domain_bounded b.domain_bounded⟩

def weightedUnit (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : GammaDefinableClosureAtBase B γ) : BoundedChart B 0 :=
  ⟨RVMeasuredCharts.weightedUnit B γ hγ, ⟨1, by intro u hu i; exact Fin.elim0 i⟩⟩

def ofRES {B : Base (M := M)} {k : ℕ} (a : RESChart B k) : BoundedChart B k :=
  ⟨a.toChart, res_domain_bounded a⟩

end DiamondIntegral.Section4.RVBoundedCharts
