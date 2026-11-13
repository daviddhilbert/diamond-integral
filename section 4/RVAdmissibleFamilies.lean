import «section 4».RVChartRestrictions
import «section 4».RVTaggedCoproductClasses

/-! Actual RV object families closed under products, definable restriction
and tagged disjoint unions. The RES and bounded families are proved
instances; invariance of the predicates under arbitrary isomorphisms is
not a premise. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVAdmissibleFamilies
open RVMeasuredCharts RVMeasuredBounds RVChartDisjointUnion RVChartRestrictions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Family (B : Base (M := M)) where
  good : ∀ k, Chart B k → Prop
  unit : good 0 (RVChartRing.unit B)
  product : ∀ k l (a : Chart B k) (b : Chart B l), good k a → good l b → good (l + k) (RVMeasuredProduct.product a b)
  restrict : ∀ n k (a : Data B n k) (I : Set (Fin n → M))
    (hI : DefinableOverBase B (fun _ : Fin n => .rv) I) (hsub : I ⊆ a.domain),
    good k a.toChart → good k (RVChartRestrictions.restrict a I hI hsub).toChart
  coproduct : ∀ k (a b : Chart B k), good k a → good k b → good k (RVTaggedCoproduct.coproduct a b)

def all (B : Base (M := M)) : Family B where
  good _ _ := True
  unit := trivial
  product _ _ _ _ _ _ := trivial
  restrict _ _ _ _ _ _ _ := trivial
  coproduct _ _ _ _ _ := trivial

def res (B : Base (M := M)) : Family B where
  good _ a := (Set.range a.valuePattern).Finite
  unit := (RESChartRing.unit B).finite_values
  product _ _ a b ha hb := RVMeasuredProductProperties.product_finite_patterns (⟨a, ha⟩ : RESChart B _) (⟨b, hb⟩ : RESChart B _)
  restrict _ _ a I hI hsub ha := restrict_finite_patterns a I hI hsub ha
  coproduct _ a b ha hb := (RVTaggedCoproductProperties.resCoproduct (⟨a, ha⟩ : RESChart B _) (⟨b, hb⟩ : RESChart B _)).finite_values

def bounded (B : Base (M := M)) : Family B where
  good _ a := DomainBounded a
  unit := (RVBoundedRing.unit B).domain_bounded
  product _ _ a b ha hb := RVMeasuredProductProperties.product_domain_bounded a b ha hb
  restrict _ _ a I hI hsub ha := restrict_domain_bounded a I hI hsub ha
  coproduct _ a b ha hb :=
    (RVTaggedCoproductProperties.boundedCoproduct (⟨a, ha⟩ : RVBoundedCharts.BoundedChart B _)
      (⟨b, hb⟩ : RVBoundedCharts.BoundedChart B _)).domain_bounded

end DiamondIntegral.Section4.RVAdmissibleFamilies
