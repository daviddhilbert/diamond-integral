import «section 3».GammaGroundGammaRVLift
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def gammaGroundRVSingleFamily (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundFiniteFamily hc B (rawRVSpace n) := ⟨1,fun _ => A⟩

def gammaGroundRVSingleFamilyBijection (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    GammaGroundBijection A (gammaGroundRVSingleFamily A).rvRealization where
  map := (gammaGroundRVFamilyTagMap (0 : Fin 1) A).corestrict (fun a => ⟨(0 : Fin 1),a,rfl⟩)
  bijective := by
    constructor
    · intro a b he
      apply Subtype.ext
      funext i
      have hh := congrArg (fun z : (gammaGroundRVSingleFamily A).rvRealization => z.val (Fin.natAdd 1 i)) he
      simpa only [GammaGroundMap.corestrict,GammaGroundMap.ofGlobal,gammaGroundRVFamilyTagMap,
        rvFamilyTagMap,rvMapOfCode,Map.ofCodes,rvAppend,Fin.append_right] using hh
    · rintro ⟨y,i,a,ha⟩
      change Fin 1 at i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact ⟨a,Subtype.ext ha⟩

def GammaGroundGammaObject.single (G : GammaGroundGammaPiece hc B n) : GammaGroundGammaObject hc B n :=
  ⟨1,fun _ => G⟩

/-- A literal full Gamma code lift agrees with the actual tagged Gamma
object lift on one piece, by an original-ground RV isomorphism. -/
def gammaGroundGammaSingleLiftBijection (G : GammaGroundGammaPiece hc B n) :
    GammaGroundBijection (gammaGroundGammaRVCodeLift G).domain (GammaGroundGammaObject.single G).rvLift.domain :=
  gammaGroundRVSingleFamilyBijection (gammaGroundGammaRVCodeLift G).domain
end DiamondIntegral.Section3
