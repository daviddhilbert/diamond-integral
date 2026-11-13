import «section 3».RVUnitGammaCodeBijection
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

/-- Units in the full value preimage agree with the complete Gamma
code presentation, retaining every representative. -/
def gammaGroundRVUnitFullCodeBijection (G : GammaGroundGammaPiece hc B n) :
    GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundCodePreimage G) :=
  (gammaGroundGammaRVCodeBijection G).symm.comp (gammaGroundRVUnitGammaCodeBijection G)

theorem gammaGroundRVUnitFullCode_decode (G : GammaGroundGammaPiece hc B n)
    (u : gammaGroundRVUnitGammaPreimage G) :
    (gammaGroundCodeDecode G ((gammaGroundRVUnitFullCodeBijection G).map u)).val = rvUnitTupleValues u.val := by
  let b := (gammaGroundRVUnitGammaCodeBijection G).map u
  let c := (gammaGroundGammaRVCodeBijection G).symm.map b
  have hb := (gammaGroundGammaRVCodeBijection G).map.apply_inverse
    (gammaGroundGammaRVCodeBijection G).bijective b
  funext i
  apply Subtype.ext
  change Values.vrv (gammaCodeTuple c.val i) = Values.vrv ((u.val i : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)
  exact congrArg Values.vrv (congrArg (fun x : (gammaGroundGammaRVCodeLift G).domain => x.val i) hb)

theorem gammaGroundRVUnitFullCode_inverse_decode (G : GammaGroundGammaPiece hc B n)
    (c : gammaGroundCodePreimage G) :
    (gammaGroundCodeDecode G c).val = rvUnitTupleValues ((gammaGroundRVUnitFullCodeBijection G).symm.map c).val := by
  have h := gammaGroundRVUnitFullCode_decode G ((gammaGroundRVUnitFullCodeBijection G).symm.map c)
  have he : (gammaGroundRVUnitFullCodeBijection G).map ((gammaGroundRVUnitFullCodeBijection G).symm.map c) = c :=
    (gammaGroundRVUnitFullCodeBijection G).map.apply_inverse (gammaGroundRVUnitFullCodeBijection G).bijective c
  rw [he] at h
  exact h
end DiamondIntegral.Section3
