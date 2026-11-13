import «section 3».GammaGroundMeasuredRVCategories
import «section 3».GammaFormOperations

/-! Constants and products of genuine Gamma forms over the complete
ground parameter base, without selecting a real representative. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {Q : Space LRV M}

def gammaGroundOneForm (A : GammaGroundDefSet hc ground Q) : GammaGroundVolumeForm hc ground A :=
  GammaGroundMap.ofGlobal A (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc))
    (gammaOneForm hc (DefSet.univ Q ground.real)) (fun _ => Set.mem_univ _)

@[simp] theorem gammaGroundOneForm_value (A : GammaGroundDefSet hc ground Q) (a : A) :
    gammaGroundFormValue (gammaGroundOneForm A) a = 1 := rfl

def GammaGroundVolumeForm.mul {A : GammaGroundDefSet hc ground Q}
    (ω σ : GammaGroundVolumeForm hc ground A) : GammaGroundVolumeForm hc ground A :=
  (GammaGroundMap.ofGlobal
    ((GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)).prod
      (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)))
    (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc))
    (gammaMultiplyMap hc ground.real) (fun _ => Set.mem_univ _)).comp (ω.pair σ)

@[simp] theorem GammaGroundVolumeForm.mul_value {A : GammaGroundDefSet hc ground Q}
    (ω σ : GammaGroundVolumeForm hc ground A) (a : A) :
    gammaGroundFormValue (ω.mul σ) a = gammaGroundFormValue ω a * gammaGroundFormValue σ a := rfl

end DiamondIntegral.Section3
