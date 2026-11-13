import «section 3».FullGammaFunctionMaps
import «section 3».GammaGroundVolumeForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {Q : Space LRV M}

def universalSingletonPower {L : Language} {N : Type} [L.Structure N]
    (P : Space L N) (S : Set N) :
    Map (DefSet.univ P S) (DefSet.univ (P.power (Fin 1)) S) :=
  Map.ofCodes _ (fun x _ => x) (fun z i => z i.2)
    (fun _ => Set.DefinableFun.proj L) (fun c _ => c.property) (fun _ => rfl)

def GammaGroundVolumeForm.inv {A : GammaGroundDefSet hc B Q}
    (ω : GammaGroundVolumeForm hc B A) : GammaGroundVolumeForm hc B A :=
  (fullGammaFunctionMap (fun γ : Fin 1 → Values.Gamma (M := M) => (γ 0)⁻¹)
    (FullGammaFunction.inv (FullGammaFunction.proj _ (0 : Fin 1)))).comp
    ((GammaGroundMap.ofGlobal _ _ (universalSingletonPower (volumeGammaSpace hc) B.real)
      (fun _ => Set.mem_univ _)).comp ω)

theorem GammaGroundVolumeForm.inv_value {A : GammaGroundDefSet hc B Q}
    (ω : GammaGroundVolumeForm hc B A) (a : A) :
    gammaGroundFormValue ω.inv a = (gammaGroundFormValue ω a)⁻¹ := rfl
end DiamondIntegral.Section3
