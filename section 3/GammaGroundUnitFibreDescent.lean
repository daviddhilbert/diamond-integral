import «section 3».RVUnitFullGammaCodes
import «section 3».GammaGroundGammaSinglePiece
import «section 3».GammaGroundGammaCodeDescent
import «section 3».GammaGroundFamilyPieceMaps
import «section 3».GammaGroundFamilyPartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

def gammaGroundUnitFullCodeTransport (G H : GammaGroundGammaPiece hc B n)
    (F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage H)) :
    GammaGroundBijection (gammaGroundCodePreimage G) (gammaGroundCodePreimage H) :=
  (gammaGroundRVUnitFullCodeBijection H).comp (F.comp (gammaGroundRVUnitFullCodeBijection G).symm)

theorem gammaGroundUnitFullCodeTransport_decode (G H : GammaGroundGammaPiece hc B n)
    (F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage H))
    (c : gammaGroundCodePreimage G) :
    (gammaGroundCodeDecode H ((gammaGroundUnitFullCodeTransport G H F).map c)).val =
      rvUnitTupleValues (F.map ((gammaGroundRVUnitFullCodeBijection G).symm.map c)).val :=
  gammaGroundRVUnitFullCode_decode H _

theorem gammaGroundGammaSingle_decode_eq_iff (G : GammaGroundGammaPiece hc B n)
    (i j : Fin 1) (c d : gammaGroundCodePreimage G) :
    (GammaGroundGammaObject.single G).decode ⟨i,c⟩ = (GammaGroundGammaObject.single G).decode ⟨j,d⟩ ↔
      (gammaGroundCodeDecode G c).val = (gammaGroundCodeDecode G d).val := by
  constructor
  · exact fun h => congrArg (fun a : (GammaGroundGammaObject.single G).Carrier => a.2.val) h
  · intro h
    exact gammaGroundFamilyCarrier_ext _ (show i = j from Subsingleton.elim i j) h

/-- A same-ground bijection of full RV value preimages that preserves
and reflects the value equivalence relation gives an actual Gamma morphism. -/
def gammaGroundGammaSingleHomOfUnitBijection (G H : GammaGroundGammaPiece hc B n)
    (F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage H))
    (hF : ∀ u v, rvUnitTupleValues u.val = rvUnitTupleValues v.val ↔
      rvUnitTupleValues (F.map u).val = rvUnitTupleValues (F.map v).val) :
    GammaGroundGammaHom (GammaGroundGammaObject.single G) (GammaGroundGammaObject.single H) := by
  let T := gammaGroundUnitFullCodeTransport G H F
  let L : GammaGroundFamilyBijection (GammaGroundGammaObject.single G).codeLift
      (GammaGroundGammaObject.single H).codeLift :=
    GammaGroundFamilyBijection.pieces (GammaGroundGammaObject.single G).codeLift
      (fun _ => gammaGroundCodePreimage H) (fun _ => T)
  apply GammaGroundGammaHom.ofCodeBijection L
  rintro ⟨i,c⟩ ⟨j,d⟩
  change (GammaGroundGammaObject.single G).decode ⟨i,c⟩ = (GammaGroundGammaObject.single G).decode ⟨j,d⟩ ↔
    (GammaGroundGammaObject.single H).decode ⟨i,T.map c⟩ = (GammaGroundGammaObject.single H).decode ⟨j,T.map d⟩
  rw [gammaGroundGammaSingle_decode_eq_iff,gammaGroundGammaSingle_decode_eq_iff,
    gammaGroundRVUnitFullCode_inverse_decode,gammaGroundRVUnitFullCode_inverse_decode,
    gammaGroundUnitFullCodeTransport_decode,gammaGroundUnitFullCodeTransport_decode]
  exact hF _ _
end DiamondIntegral.Section3
