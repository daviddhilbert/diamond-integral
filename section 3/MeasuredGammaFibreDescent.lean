import «section 3».GammaGroundUnitFibreDescent
import «section 3».GammaGroundMeasuredGammaSingleWeight
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

/-- A full-fibre RV bijection preserving the value equivalence and the
prescribed combined weights gives a genuine measured Gamma morphism,
including its actual RV code contraction over the same ground. -/
def gammaGroundMeasuredGammaSingleHomOfWeightUnitBijection
    (G H : GammaGroundGammaPiece hc B n)
    (F : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage H))
    (hF : ∀ u v, rvUnitTupleValues u.val = rvUnitTupleValues v.val ↔
      rvUnitTupleValues (F.map u).val = rvUnitTupleValues (F.map v).val)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (hh : FullGammaFunction (integrationGammaBase B) h)
    (hw : ∀ u, f (rvUnitTupleValues u.val) = h (rvUnitTupleValues (F.map u).val)) :
    GammaGroundMeasuredGammaHom (gammaGroundMeasuredGammaSingleWeight G f hf)
      (gammaGroundMeasuredGammaSingleWeight H h hh) := by
  let T := gammaGroundUnitFullCodeTransport G H F
  let L : GammaGroundFamilyBijection (GammaGroundGammaObject.single G).codeLift
      (GammaGroundGammaObject.single H).codeLift :=
    GammaGroundFamilyBijection.pieces (GammaGroundGammaObject.single G).codeLift
      (fun _ => gammaGroundCodePreimage H) (fun _ => T)
  apply gammaGroundMeasuredGammaHomOfCodes L
  · rintro ⟨i,c⟩ ⟨j,d⟩
    change (GammaGroundGammaObject.single G).decode ⟨i,c⟩ = (GammaGroundGammaObject.single G).decode ⟨j,d⟩ ↔
      (GammaGroundGammaObject.single H).decode ⟨i,T.map c⟩ = (GammaGroundGammaObject.single H).decode ⟨j,T.map d⟩
    rw [gammaGroundGammaSingle_decode_eq_iff,gammaGroundGammaSingle_decode_eq_iff,
      gammaGroundRVUnitFullCode_inverse_decode,gammaGroundRVUnitFullCode_inverse_decode,
      gammaGroundUnitFullCodeTransport_decode,gammaGroundUnitFullCodeTransport_decode]
    exact hF _ _
  · rintro ⟨i,c⟩
    rw [gammaGroundMeasuredGammaSingleWeight_combined,gammaGroundMeasuredGammaSingleWeight_combined]
    change f (gammaGroundCodeDecode G c).val = h (gammaGroundCodeDecode H (T.map c)).val
    rw [gammaGroundRVUnitFullCode_inverse_decode,gammaGroundUnitFullCodeTransport_decode]
    exact hw _
end DiamondIntegral.Section3
