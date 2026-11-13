import «section 3».GammaGroundDefSets
import «section 3».NamedDefinableMaps

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Q R T U : Space LRV M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {ground : GammaParameters.Base (M := M)}

structure GammaGroundMap (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) where
  toFun : A → B
  graph_definable : GammaGroundDefinable hc ground (Q.prod R)
    {z | ∃ a : A, a.val = z.1 ∧ (toFun a).val = z.2}

instance gammaGroundMapCoeFun {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} :
    CoeFun (GammaGroundMap A B) (fun _ => A → B) := ⟨GammaGroundMap.toFun⟩

@[ext] theorem GammaGroundMap.ext {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    {f g : GammaGroundMap A B} (h : ∀ a, f a = g a) : f = g := by
  have he : f.toFun = g.toFun := funext h
  cases f
  cases g
  cases he
  rfl

def GammaGroundMap.id (A : GammaGroundDefSet hc ground Q) : GammaGroundMap A A where
  toFun a := a
  graph_definable := by
    have hA := A.definable.preimage (universalProductFst Q Q ground.real)
    have hE : GammaGroundDefinable hc ground (Q.prod Q) {z | z.1 = z.2} :=
      GammaGroundDefinable.of_real ((relationDefinable_iff_product Eq).mp (Q.relation_eq_definable ground.real))
    apply (hA.inter hE).congr
    intro z
    constructor
    · rintro ⟨ha, he⟩
      exact ⟨⟨z.1, ha⟩, rfl, he⟩
    · rintro ⟨a, ha, hb⟩
      refine ⟨?_, ha.symm.trans hb⟩
      change z.1 ∈ A.carrier
      exact ha ▸ a.property


end DiamondIntegral.Section3
