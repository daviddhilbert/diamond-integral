import «section 3».GammaGroundBijections
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}

def GammaGroundBijection.ofEmpty (hA : A.carrier = ∅) (hB : B.carrier = ∅) : GammaGroundBijection A B := by
  have ha : ∀ a : A, False := fun a => (Set.eq_empty_iff_forall_notMem.mp hA) a.val a.property
  have hb : ∀ b : B, False := fun b => (Set.eq_empty_iff_forall_notMem.mp hB) b.val b.property
  refine ⟨{toFun := fun a => False.elim (ha a),graph_definable := ?_},
    ⟨fun a => False.elim (ha a),fun b => False.elim (hb b)⟩⟩
  apply (GammaGroundDefSet.empty hc ground (P.prod Q)).definable.congr
  intro z
  constructor
  · exact False.elim
  · rintro ⟨a,_,_⟩
    exact False.elim (ha a)
end DiamondIntegral.Section3
