import «section 3».GammaMeasuredRVSyntax
import «section 3».GammaGroundMeasuredRVCategories

/-! The native Gamma chart's product tuple is exactly the combined
measured Gamma weight for every representative of the density value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {d : ℕ}

theorem gammaVolumeCodeRV_value (c : (volumeGammaSpace hc).domain) :
    Values.vrv (gammaVolumeCodeRV c 0) =
      (cast (gammaCarrier hc) ((volumeGammaSpace hc).decode c)).val := rfl

theorem gammaMeasuredCodeProduct_raw (v : Fin d → CanonicalRV.RVSort M)
    (c : (volumeGammaSpace hc).domain) :
    rvValues (Fin.append v (gammaVolumeCodeRV c)) = Fin.append (rvValues v) c.val := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rvValues,Fin.append_left,Fin.append_right,gammaVolumeCodeRV]

theorem gammaMeasuredCodeProduct
    {Q : Space LRV M} {A : GammaGroundDefSet hc B Q}
    (ω : GammaGroundVolumeForm hc B A) (u : A)
    (v : Fin d → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain)
    (hCode : (volumeGammaSpace hc).decode c = (ω u).val) :
    Values.vrv (∏ i, Fin.append v (gammaVolumeCodeRV c) i) =
      (gammaGroundFormValue ω u).val * ∏ i, Values.vrv (v i) := by
  calc
    Values.vrv (∏ i, Fin.append v (gammaVolumeCodeRV c) i) =
        ∏ i, Values.vrv (Fin.append v (gammaVolumeCodeRV c) i) :=
      map_prod RVOperations.vrvHom _ _
    _ = (∏ i, Values.vrv (v i)) * Values.vrv (gammaVolumeCodeRV c 0) := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left,Fin.append_right,Fin.prod_univ_one]
    _ = (gammaGroundFormValue ω u).val * ∏ i, Values.vrv (v i) := by
      rw [gammaVolumeCodeRV_value,hCode]
      exact mul_comm _ _

end DiamondIntegral.Section3
