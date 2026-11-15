import «section 5».RESGroundTransfer
import «section 4».RVOrdinaryRing
import «section 4».RVOrdinaryMaps
import «section 4».GammaOrdinarySharpRingMap

/-! Actual original-parameter substitution on ordinary RV charts. -/
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

def rvGroundTransferInvariant : RVOrdinaryRing.Invariant B (RVOrdinaryRing.Ring C) where
  value _ a := RVOrdinaryRing.objectClass (resGroundTransferChart H a)
  unit := by
    exact (RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap _ _ id
      (RVSharpCharts.identity_graph_definable C _ (H _ _ (RVChartRing.unit B).domain_definable))
      (Set.bijOn_id _))).trans (RVOrdinaryRing.objectClass_unit C)
  product _ _ a b := by
    exact (RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap
      (resGroundTransferChart H (RVMeasuredProduct.product a b))
      (RVMeasuredProduct.product (resGroundTransferChart H a) (resGroundTransferChart H b)) id
      (RVSharpCharts.identity_graph_definable C _ (H _ _ (RVMeasuredProduct.product a b).domain_definable))
      (Set.bijOn_id _))).trans (RVOrdinaryRing.objectClass_product (resGroundTransferChart H a) (resGroundTransferChart H b))
  iso _ _ _ f := RVOrdinaryRing.objectClass_iso (RVUnderlyingIsomorphisms.toFixed
    (resGroundTransferIso H (RVUnderlyingIsomorphisms.ofFixed f)))
  empty _ a h := RVOrdinaryRing.objectClass_empty (resGroundTransferChart H a) h
  scissor _ a b c d h := RVOrdinaryRing.objectClass_scissor _ _ _ _ h

def rvGroundTransferOrdinary : RVOrdinaryRing.Ring B →+* RVOrdinaryRing.Ring C :=
  RVOrdinaryRing.lift B (rvGroundTransferInvariant H)

theorem rvGroundTransferOrdinary_class {k : ℕ} (a : Chart B k) :
    rvGroundTransferOrdinary H (RVOrdinaryRing.objectClass a) =
      RVOrdinaryRing.objectClass (resGroundTransferChart H a) :=
  RVOrdinaryRing.lift_objectClass B (rvGroundTransferInvariant H) a

theorem rvGroundTransferOrdinary_res (x : RESOrdinaryRing.Ring B) :
    rvGroundTransferOrdinary H (RVOrdinaryMaps.ofRES B x) =
      RVOrdinaryMaps.ofRES C (resGroundTransferOrdinary H x) := by
  have h : (rvGroundTransferOrdinary H).comp (RVOrdinaryMaps.ofRES B) =
      (RVOrdinaryMaps.ofRES C).comp (resGroundTransferOrdinary H) := by
    apply RESOrdinaryRing.hom_ext B
    intro k a
    change rvGroundTransferOrdinary H (RVOrdinaryMaps.ofRES B (RESOrdinaryRing.objectClass a)) = _
    rw [RVOrdinaryMaps.ofRES_class,rvGroundTransferOrdinary_class]
    change _ = RVOrdinaryMaps.ofRES C (resGroundTransferOrdinary H (RESOrdinaryRing.objectClass a))
    rw [resGroundTransferOrdinary_class,RVOrdinaryMaps.ofRES_class]
    rfl
  exact RingHom.congr_fun h x

theorem resGroundTransferReduced_fromOrdinary (x : RESOrdinaryRing.Ring B) :
    resGroundTransferReduced H (RESDimensionFreeReduction.fromOrdinary B x) =
      RESDimensionFreeReduction.fromOrdinary C (resGroundTransferOrdinary H x) := rfl

end DiamondIntegral.Section5
