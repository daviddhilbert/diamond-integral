import «section 3».GammaGroundRVUnitProducts
import «section 3».GammaGroundRVUnitRES
import «section 3».GammaGroundGammaRVCodeMembership
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {m : ℕ}

def gammaGroundRVUnitGammaCodeMap (G : GammaGroundGammaPiece hc B m) :
    GammaGroundMap (gammaGroundRVUnitGammaPreimage G) (gammaGroundGammaRVCodeLift G).domain :=
  GammaGroundMap.ofGlobal _ _ (rvUnitToRVMap (DefSet.univ (rawRVUnitSpace m) B.real)) (fun u =>
    (gammaGroundGammaRVCodeLift_mem G _).mpr ⟨rvUnitTupleValues u.val,u.property,fun _ => rfl⟩)

/-- The full unit-fibre factor is bijective with the paper's literal
Gamma-to-RV code lift, retaining all representatives. -/
def gammaGroundRVUnitGammaCodeBijection (G : GammaGroundGammaPiece hc B m) :
    GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundGammaRVCodeLift G).domain where
  map := gammaGroundRVUnitGammaCodeMap G
  bijective := by
    constructor
    · intro x y he
      apply Subtype.ext
      funext i
      apply Units.ext
      exact congrArg (fun z : (gammaGroundGammaRVCodeLift G).domain => z.val i) he
    · intro a
      have ha0 : ∀ i, a.val i ≠ 0 := by
        intro i hi
        exact (gammaGroundGammaRVCodeLift G).nonzero a i ((congrArg Subtype.val hi).trans RVOperations.zero_val)
      let u : Fin m → (CanonicalRV.RVSort M)ˣ := fun i => Units.mk0 (a.val i) (ha0 i)
      obtain ⟨δ,hδ,hval⟩ := (gammaGroundGammaRVCodeLift_mem G a.val).mp a.property
      have hu : rvUnitTupleValues u = δ := by
        funext i
        apply Subtype.ext
        exact (hval i).symm
      have huG : u ∈ (gammaGroundRVUnitGammaPreimage G).carrier := by
        change rvUnitTupleValues u ∈ G.carrier
        rwa [hu]
      exact ⟨⟨u,huG⟩,Subtype.ext rfl⟩
end DiamondIntegral.Section3
