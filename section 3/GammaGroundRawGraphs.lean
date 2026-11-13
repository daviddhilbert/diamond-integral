import «section 3».GammaGroundRawLogic
import «section 3».GammaGroundMaps

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M} {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}

def GammaGroundMap.graph (f : GammaGroundMap A B) (x : Q.Carrier) (y : R.Carrier) : Prop :=
  ∃ a : A, a.val = x ∧ (f a).val = y

theorem GammaGroundMap.raw_graph_definable (f : GammaGroundMap A B) :
    GammaGroundRawDefinable hc ground (Q.relation R f.graph) := by
  have h := f.graph_definable.on_real_codes
  apply h.congr
  intro z
  constructor
  · rintro ⟨⟨hq, hr⟩, h⟩
    exact ⟨hq, hr, h⟩
  · rintro ⟨hq, hr, h⟩
    exact ⟨⟨hq, hr⟩, h⟩

end DiamondIntegral.Section3
