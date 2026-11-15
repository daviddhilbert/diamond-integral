import «section 5».VFFieldGamma
import «section 5».VFFieldSmallPresentation
import «section 3».GammaGroundContext

/-! The exact actual field and its value group instantiate all standing
Section 3 context hypotheses in the same saturated ambient model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV ValuedModelMap DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def vfFieldContext (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (F : Subfield (VFType (M := M))) (hF : Cardinal.mk F < G.κ)
    (hnt : ∃ x : Fˣ,vfFieldGammaMap F x ≠ 1) : GammaGroundContext M where
  model00 := G.model00
  κ := G.κ
  uncountable := G.uncountable
  saturated := G.saturated
  homogeneous := G.homogeneous
  real := vfFieldSubstructure hc F
  fieldBase := vfFieldSubstructureBase hc F
  gamma := vfFieldGamma F
  values_mem := vfFieldGamma_values_mem F hc
  small_real := vfFieldSubstructure_small hc F G.uncountable.le hF
  small_gamma := vfFieldGamma_small F hF
  nontrivial_gamma := by
    obtain ⟨x,hx⟩ := hnt
    exact ⟨⟨vfFieldGammaMap F x,⟨x,rfl⟩⟩,hx⟩

end DiamondIntegral.Section5
