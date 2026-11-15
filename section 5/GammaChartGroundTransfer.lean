import «section 5».RVOrdinaryGroundTransfer
import «section 5».NativeBoundedRetraction

/-! Parameter substitution retains literal Gamma supports and their
full RV preimages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

def gammaGroundTransferChart {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) : GammaOrdinaryCharts.Chart C n :=
  ⟨a.support,H _ _ a.support_definable⟩

theorem rvGroundTransferOrdinary_sharp_chart {n : ℕ} (a : GammaOrdinaryCharts.Chart B n) :
    rvGroundTransferOrdinary H (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a)) =
      GammaOrdinarySharpRingMap.sharp C (GammaOrdinaryRing.objectClass (gammaGroundTransferChart H a)) := by
  rw [GammaOrdinarySharpRingMap.sharp_class,rvGroundTransferOrdinary_class,GammaOrdinarySharpRingMap.sharp_class]
  exact RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable C _ (H _ _ (GammaOrdinaryCharts.sharpChart a).domain_definable))
    (Set.bijOn_id _))

theorem resGroundTransferReduced_torus :
    resGroundTransferReduced H (nativeTorusClass B) = nativeTorusClass C := by
  change resGroundTransferReduced H (RESDimensionFreeReduction.fromOrdinary B
    (RESOrdinaryRing.objectClass (RESFibreObjects.torus B))) = _
  rw [resGroundTransferReduced_fromOrdinary,resGroundTransferOrdinary_class]
  apply congrArg (RESDimensionFreeReduction.fromOrdinary C)
  exact RESOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable C _ (H _ _ (RESFibreObjects.torus B).domain_definable))
    (Set.bijOn_id _))

end DiamondIntegral.Section5
