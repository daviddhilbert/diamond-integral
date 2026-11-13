import «section 3».GammaGroundGammaSinglePiece
import «section 3».GammaGroundMeasuredGammaRVLift
import «section 3».FullGammaFunctionMaps
import «section 3».FullGammaFunctionComposition
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

/-- The full Gamma factor with a prescribed combined weight, retaining
all finite and zero-dimensional Gamma forms. -/
def gammaGroundMeasuredGammaSingleWeight (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) : GammaGroundMeasuredGammaObject hc B n where
  underlying := GammaGroundGammaObject.single G
  form _ := (fullGammaFunctionMap (fun γ => f γ * (∏ i, γ i)⁻¹)
    (hf.mul (FullGammaFunction.inv
      (FullGammaFunction.prod Finset.univ (fun i γ => γ i) (fun i _ => FullGammaFunction.proj _ i))))).restrict
      (fun _ _ => Set.mem_univ _)

theorem gammaGroundMeasuredGammaSingleWeight_combined (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (a : (gammaGroundMeasuredGammaSingleWeight G f hf).underlying.Carrier) :
    (gammaGroundMeasuredGammaSingleWeight G f hf).combinedWeight a = f a.2.val := by
  change (f a.2.val * (∏ i, cast (gammaCarrier hc) (a.2.val i))⁻¹) *
    (∏ i, cast (gammaCarrier hc) (a.2.val i)) = f a.2.val
  exact inv_mul_cancel_right _ _
end DiamondIntegral.Section3
