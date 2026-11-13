import «section 3».GammaGroundMeasuredGammaSingleWeight
import «section 3».RVUnitGammaCodeBijection
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaGroundGammaUnitLiftBijection (G : GammaGroundGammaPiece hc B n) :
    GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (GammaGroundGammaObject.single G).rvLift.domain :=
  (gammaGroundGammaSingleLiftBijection G).comp (gammaGroundRVUnitGammaCodeBijection G)

/-- The prescribed Gamma weight is exactly the weight on every RV
representative in the actual lifted Gamma factor. -/
theorem gammaGroundMeasuredGammaUnitLift_combined (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (u : gammaGroundRVUnitGammaPreimage G) :
    (gammaGroundMeasuredGammaSingleWeight G f hf).rvLift.combinedWeight
      ((gammaGroundGammaUnitLiftBijection G).map u) = f (rvUnitTupleValues u.val) := by
  let J := gammaGroundMeasuredGammaSingleWeight G f hf
  let b := (gammaGroundRVUnitGammaCodeBijection G).map u
  let c := (gammaGroundGammaRVCodeBijection G).symm.map b
  let d : J.underlying.codeLift.Carrier := ⟨(0 : Fin 1),c⟩
  have he : J.underlying.rvEncodeCode d = (gammaGroundGammaUnitLiftBijection G).map u := by
    change J.underlying.rvPieces.rvEncode
      ⟨(0 : Fin 1),(gammaGroundGammaRVCodeBijection G).map c⟩ = _
    rw [show (gammaGroundGammaRVCodeBijection G).map c = b from
      (gammaGroundGammaRVCodeBijection G).map.apply_inverse _ b]
    rfl
  have hv : (J.underlying.decode d).2.val = rvUnitTupleValues u.val := by
    have hb := (gammaGroundGammaRVCodeBijection G).map.apply_inverse
      (gammaGroundGammaRVCodeBijection G).bijective b
    funext i
    apply Subtype.ext
    change Values.vrv (gammaCodeTuple c.val i) = Values.vrv ((u.val i : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)
    exact congrArg Values.vrv (congrArg (fun x : (gammaGroundGammaRVCodeLift G).domain => x.val i) hb)
  rw [← he,gammaGroundMeasuredGammaLift_combined,gammaGroundMeasuredGammaSingleWeight_combined,hv]
end DiamondIntegral.Section3
