import «section 3».GammaGroundMapRestrictions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

/-- A point whose singleton is definable over the original Gamma ground
supplies a constant map over exactly that ground. -/
def GammaGroundMap.const (A : GammaGroundDefSet hc B Q) (c : R.Carrier)
    (hcdef : GammaGroundDefinable hc B R {c}) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B R) where
  toFun _ := ⟨c,Set.mem_univ _⟩
  graph_definable := by
    have ha := A.definable.preimage (universalProductFst Q R B.real)
    have hc := hcdef.preimage (universalProductSnd Q R B.real)
    apply (ha.inter hc).congr
    intro z
    constructor
    · rintro ⟨hz,hc⟩
      exact ⟨⟨z.1,hz⟩,rfl,hc.symm⟩
    · rintro ⟨a,ha,hc⟩
      refine ⟨?_,hc.symm⟩
      change z.1 ∈ A.carrier
      exact ha ▸ a.property
end DiamondIntegral.Section3
