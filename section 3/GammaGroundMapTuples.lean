import «section 3».GammaGroundFiniteCoverPartition
import «section 3».GammaGroundMapProducts
import «section 3».PowerProjectionMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3

section Coordinates
variable {L : Language} {M : Type} [L.Structure M]
def universalPowerCoordinate (P : Space L M) (S : Set M) {I : Type} [Finite I] (i : I) :
    Map (DefSet.univ (P.power I) S) (DefSet.univ P S) :=
  Map.ofCodes _ (fun x => x i) (fun c j => c (i,j))
    (fun _ => Set.DefinableFun.proj L) (fun c => c.property i) (fun _ => rfl)
end Coordinates

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M} {A : GammaGroundDefSet hc B Q}

/-- Finite tuples of actual interpreted maps retain complete original
code graphs, including the empty output tuple. -/
def GammaGroundMap.tuple {I : Type} [Finite I]
    (f : I → GammaGroundMap A (GammaGroundDefSet.univ hc B R)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (R.power I)) where
  toFun a := ⟨fun i => (f i a).val,Set.mem_univ _⟩
  graph_definable := by
    have hF (i : I) : GammaGroundDefinable hc B (Q.prod (R.power I))
        {z | ∃ a : A, a.val = z.1 ∧ (f i a).val = z.2 i} :=
      (f i).graph_definable.preimage
        (((universalProductFst Q (R.power I) B.real).pair
          ((universalPowerCoordinate R B.real i).comp
            (universalProductSnd Q (R.power I) B.real))).toUniv)
    have hA := A.definable.preimage (universalProductFst Q (R.power I) B.real)
    apply (hA.inter (GammaGroundDefinable.iInter hF)).congr
    intro z
    constructor
    · rintro ⟨ha,h⟩
      let a : A := ⟨z.1,ha⟩
      refine ⟨a,rfl,?_⟩
      funext i
      obtain ⟨b,hb,hf⟩ := Set.mem_iInter.mp h i
      have hba : b = a := Subtype.ext hb
      exact (congrArg (fun t : A => (f i t).val) hba).symm.trans hf
    · rintro ⟨a,ha,hf⟩
      have hza : z.1 ∈ A.carrier := ha ▸ a.property
      refine ⟨hza,?_⟩
      exact Set.mem_iInter.mpr (fun i => ⟨a,ha,congrFun hf i⟩)

@[simp] theorem GammaGroundMap.tuple_value {I : Type} [Finite I]
    (f : I → GammaGroundMap A (GammaGroundDefSet.univ hc B R)) (a : A) (i : I) :
    (GammaGroundMap.tuple f a).val i = (f i a).val := rfl

end DiamondIntegral.Section3
