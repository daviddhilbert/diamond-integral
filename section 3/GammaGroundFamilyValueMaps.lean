import «section 3».GammaGroundFamilyMaps
import «section 3».GammaGroundFiniteCoverPartition
import «section 3».GammaGroundMapRelations
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
variable {P Q : Space LRV M}
variable {A : GammaGroundFiniteFamily hc B P} {D : GammaGroundFiniteFamily hc B Q}

/-- Forgetting the finite output tag preserves the complete same-ground
graph of an actual family map, by finite union of its branches. -/
def GammaGroundFamilyMap.valueMap (F : GammaGroundFamilyMap A D) (i : Fin A.tags) :
    GammaGroundMap (A.piece i) (GammaGroundDefSet.univ hc B Q) where
  toFun a := ⟨(F.toFun ⟨i,a⟩).2.val,Set.mem_univ _⟩
  graph_definable := by
    have h := GammaGroundRelationDefinable.exists_finite (fun j => F.definable i j)
    apply GammaGroundDefinable.congr h
    intro z
    constructor
    · rintro ⟨j,a,b,ha,hb,hf⟩
      refine ⟨a,ha,?_⟩
      exact (congrArg (fun t : D.Carrier => t.2.val) hf).trans hb
    · rintro ⟨a,ha,hf⟩
      let v := F.toFun ⟨i,a⟩
      exact ⟨v.1,a,v.2,ha,hf,rfl⟩

@[simp] theorem GammaGroundFamilyMap.valueMap_value
    (F : GammaGroundFamilyMap A D) (i : Fin A.tags) (a : A.piece i) :
    (F.valueMap i a).val = (F.toFun ⟨i,a⟩).2.val := rfl

end DiamondIntegral.Section3
