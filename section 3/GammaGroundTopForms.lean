import «section 3».GammaTopPresentation
import «section 3».GammaGroundVolumeForms

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
variable {Q : Space LRV M} {A : GammaGroundDefSet hc ground Q}

abbrev GammaGroundTopForm (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) {Q : Space LRV M} (A : GammaGroundDefSet hc ground Q) :=
  GammaGroundMap A (GammaGroundDefSet.univ hc ground gammaTopSpace)

def GammaGroundVolumeForm.toTop (ω : GammaGroundVolumeForm hc ground A) : GammaGroundTopForm hc ground A :=
  (GammaGroundMap.ofGlobal _ _ (gammaIncludeTopMap hc ground.real) (fun _ => Set.mem_univ _)).comp ω

@[simp] theorem GammaGroundVolumeForm.toTop_value (ω : GammaGroundVolumeForm hc ground A) (a : A) :
    (ω.toTop a).val = (gammaGroundFormValue ω a).val := rfl

def GammaGroundTopForm.mul (ω σ : GammaGroundTopForm hc ground A) : GammaGroundTopForm hc ground A :=
  (GammaGroundMap.ofGlobal _ _ (gammaTopMultiplyMap ground.real) (fun _ => Set.mem_univ _)).comp (ω.pair σ)

@[simp] theorem GammaGroundTopForm.mul_value (ω σ : GammaGroundTopForm hc ground A) (a : A) :
    (ω.mul σ a).val = (show Values.GammaTop (M := M) from (ω a).val) *
      (show Values.GammaTop (M := M) from (σ a).val) := rfl

def GammaGroundMap.valuation (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawVFSpace 1))) :
    GammaGroundTopForm hc ground A :=
  (GammaGroundMap.ofGlobal _ _ (gammaTopValuationMap ground.real) (fun _ => Set.mem_univ _)).comp f

@[simp] theorem GammaGroundMap.valuation_value
    (f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawVFSpace 1))) (a : A) :
    (f.valuation a).val = Values.vfValueHom ((f a).val 0) := rfl

end DiamondIntegral.Section3
