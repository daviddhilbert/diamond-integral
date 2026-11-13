import «section 3».GammaGroundMapImages
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
variable {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
theorem GammaGroundMap.definable_preimage (f : GammaGroundMap A B)
    {T : Set Q.Carrier} (hT : GammaGroundDefinable hc ground Q T) :
    GammaGroundDefinable hc ground P {x | ∃ a : A, a.val = x ∧ (f a).val ∈ T} := by
  have hd := f.graph_definable.inter (hT.preimage (universalProductSnd P Q ground.real))
  apply (hd.image (universalProductFst P Q ground.real)).congr
  intro x
  constructor
  · rintro ⟨z, ⟨⟨a, ha, hf⟩, ht⟩, hx⟩
    exact ⟨a, ha.trans hx, hf.symm ▸ ht⟩
  · rintro ⟨a, ha, ht⟩
    exact ⟨(a.val, (f a).val), ⟨⟨a, rfl, rfl⟩, ht⟩, ha⟩
/-- Actual preimage inside the partial map's source domain. -/
def GammaGroundMap.preimage (f : GammaGroundMap A B) (T : GammaGroundDefSet hc ground Q) :
    GammaGroundDefSet hc ground P :=
  ⟨{x | ∃ a : A, a.val = x ∧ (f a).val ∈ T.carrier}, f.definable_preimage T.definable⟩

theorem GammaGroundMap.preimage_subset (f : GammaGroundMap A B) (T : GammaGroundDefSet hc ground Q) :
    (f.preimage T).carrier ⊆ A.carrier := by
  rintro x ⟨a,ha,_⟩
  exact ha ▸ a.property

end DiamondIntegral.Section3
