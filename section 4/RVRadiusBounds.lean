import «section 4».RVRadiusGenerators
import «section 4».RVMeasuredBounds

/-! The actual radius-generator charts are doubly bounded. Their classes
therefore lie in the additive span of bounded chart classes in the ambient
scissors group. This span is not asserted to be an injective presentation
of the bounded category, and no product ideal is constructed here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVRadiusBounds
open RVMeasuredCharts RVMeasuredGroup RVMeasuredBounds RVRadiusGenerators
open RVSharpCharts RVPointChoices GammaRVLifts GammaRadiusAnnulus

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def boundedSpan (B : Base (M := M)) (k : ℕ) : AddSubgroup (KGroup B k) :=
  AddSubgroup.closure {x | ∃ a : Chart B k, DomainBounded a ∧ x = objectClass a}

theorem boundedClass_mem {B : Base (M := M)} {k : ℕ} (a : Chart B k) (ha : DomainBounded a) :
    objectClass a ∈ boundedSpan B k := AddSubgroup.subset_closure ⟨a, ha, rfl⟩

theorem annulus_domain_bounded (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : DomainBounded (sharpChart (annulusChart B γ hγ)) :=
  sharp_domain_bounded (annulusChart B γ hγ) (annulus_bounded γ hγ.1)

theorem point_domain_bounded (B : Base (M := M)) (t : Code (M := M))
    (ht : DefinableClosureAtBase B .rv (raw t)) : DomainBounded (pointChart B t ht) :=
  res_domain_bounded (pointRESChart B t ht)

theorem radiusGenerator_mem_boundedSpan (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) (t : RadiusLift B γ) : radiusGenerator B γ hγ t ∈ boundedSpan B 1 := by
  have ha := boundedClass_mem (sharpChart (annulusChart B γ hγ)) (annulus_domain_bounded B γ hγ)
  have ht := boundedClass_mem (pointChart B t.point t.definable) (point_domain_bounded B t.point t.definable)
  have h1 := boundedClass_mem (pointChart B oneCode (oneCode_definable B))
    (point_domain_bounded B oneCode (oneCode_definable B))
  exact (boundedSpan B 1).sub_mem ((boundedSpan B 1).add_mem ha ht) h1

theorem pGamma_mem_boundedSpan (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : pGamma B γ hγ ∈ boundedSpan B 1 :=
  radiusGenerator_mem_boundedSpan B γ hγ _

end DiamondIntegral.Section4.RVRadiusBounds
