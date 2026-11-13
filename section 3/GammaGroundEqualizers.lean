import «section 3».GammaGroundMapPreimages

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

def GammaGroundMap.equalizer (f g : GammaGroundMap A B) : GammaGroundDefSet hc ground Q where
  carrier := {x | ∃ a : A, a.val = x ∧ (f a).val = (g a).val}
  definable := by
    have he : GammaGroundDefinable hc ground (R.prod R) {z | z.1 = z.2} :=
      GammaGroundDefinable.of_real ((relationDefinable_iff_product Eq).mp (R.relation_eq_definable ground.real))
    exact (f.pair g).definable_preimage he

theorem GammaGroundMap.equalizer_subset (f g : GammaGroundMap A B) : (f.equalizer g).carrier ⊆ A.carrier := by
  rintro x ⟨a, rfl, _⟩
  exact a.property

end DiamondIntegral.Section3
