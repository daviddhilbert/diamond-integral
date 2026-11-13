import «section 3».GammaGroundGammaProducts
import «section 3».FullGammaFunctionMaps
import «section 3».GammaGroundMapTuples
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- The interpreted slice gamma -> (gamma,1) has its entire old-ground
code graph. Its additional coordinate is the identity, not a chosen RV
representative of a varying Gamma value. -/
def gammaGroundGammaUnitSlice (I : GammaGroundGammaPiece hc B n) (m : ℕ) :
    GammaGroundMap I (gammaGroundGammaAppendMap I
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).image := by
  let oneMap : GammaGroundMap I (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
    (fullGammaFunctionMap (fun _ : Fin n → Values.Gamma (M := M) => 1) (FullGammaFunction.one _)).restrict
      (fun _ _ => Set.mem_univ _)
  let ones := GammaGroundMap.tuple (fun _ : Fin m => oneMap)
  exact (gammaGroundGammaAppendMap I
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin m)))).toImage.comp
      ((GammaGroundMap.id I).pair ones)

@[simp] theorem gammaGroundGammaUnitSlice_formula (I : GammaGroundGammaPiece hc B n) (m : ℕ) (γ : I) :
    (gammaGroundGammaUnitSlice I m γ).val = Fin.append γ.val (fun _ => (1 : Values.Gamma (M := M))) := rfl

end DiamondIntegral.Section3
