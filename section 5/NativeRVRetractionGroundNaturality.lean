import «section 5».RVRetractionGroundNaturality
import «section 5».NativeRVGroundTransfer
import «section 5».NativeRVObjectEvaluation

/-! The same naturality square for actual native Section 3 RV objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)

theorem rvGroundTransferOrdinary_nativeChart {k : ℕ} (U : GammaGroundRVObject hc B k) :
    rvGroundTransferOrdinary H (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart U)) =
      RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (sortedTransferRVObject H U)) := by
  rw [rvGroundTransferOrdinary_class]
  exact RVOrdinaryRing.objectClass_iso (RVForgetScissors.ofMap _ _ id
    (RVSharpCharts.identity_graph_definable C _ (H _ _ (Section3RVChartBridge.chart U).domain_definable))
    (Set.bijOn_id _))

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hrB : Cardinal.mk B.real < κ) (hγB : Cardinal.mk B.gamma < κ) (hΓB : Section2.NontrivialDefinableGamma B)
variable (hrC : Cardinal.mk C.real < κ) (hγC : Cardinal.mk C.gamma < κ) (hΓC : Section2.NontrivialDefinableGamma C)
variable (kind : EulerKind)

theorem nativeGroundRVEvaluation_parameter_naturality {k : ℕ} (U : GammaGroundRVObject hc B k) :
    resGroundTransferReduced H (nativeGroundRVEvaluation h00 linear hκ hs hc B hrB hγB hΓB kind (ordinaryClass U)) =
      nativeGroundRVEvaluation h00 linear hκ hs hc C hrC hγC hΓC kind (ordinaryClass (sortedTransferRVObject H U)) := by
  rw [nativeGroundRVEvaluation_class,nativeGroundRVEvaluation_class]
  exact (nativeRVEvaluation_parameter_naturality H h00 linear hκ hs hrB hγB hΓB hrC hγC hΓC kind _).trans
    (congrArg (nativeRVEvaluation h00 linear hκ hs hc C hrC hγC hΓC kind) (rvGroundTransferOrdinary_nativeChart H U))

end DiamondIntegral.Section5
