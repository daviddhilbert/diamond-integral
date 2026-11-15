import «section 5».RVRetractionExt
import «section 5».GammaChartGroundTransfer
import «section 5».GammaIntegralBaseIndependence

/-! Both ungraded RV retractions commute with actual equivalent
parameter substitution. This compares the real quotient-ring maps,
not only chosen positive representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hrB : Cardinal.mk B.real < κ) (hγB : Cardinal.mk B.gamma < κ) (hΓB : Section2.NontrivialDefinableGamma B)
variable (hrC : Cardinal.mk C.real < κ) (hγC : Cardinal.mk C.gamma < κ) (hΓC : Section2.NontrivialDefinableGamma C)
variable (kind : EulerKind)

theorem nativeRVEvaluation_parameter_naturality (x : RVOrdinaryRing.Ring B) :
    resGroundTransferReduced H (nativeRVEvaluation h00 linear hκ hs hc B hrB hγB hΓB kind x) =
      nativeRVEvaluation h00 linear hκ hs hc C hrC hγC hΓC kind (rvGroundTransferOrdinary H x) := by
  have he : (resGroundTransferReduced H).comp (nativeRVEvaluation h00 linear hκ hs hc B hrB hγB hΓB kind) =
      (nativeRVEvaluation h00 linear hκ hs hc C hrC hγC hΓC kind).comp (rvGroundTransferOrdinary H) := by
    apply rvOrdinaryRetraction_ext (Section3T001Integration.ordinary (hc := hc) hκ hs h00 hrB hγB hΓB)
    · intro r
      change resGroundTransferReduced H (nativeRVEvaluation h00 linear hκ hs hc B hrB hγB hΓB kind (RVOrdinaryMaps.ofRES B r)) =
        nativeRVEvaluation h00 linear hκ hs hc C hrC hγC hΓC kind (rvGroundTransferOrdinary H (RVOrdinaryMaps.ofRES B r))
      rw [nativeRVEvaluation_res,rvGroundTransferOrdinary_res,nativeRVEvaluation_res,resGroundTransferReduced_fromOrdinary]
    · intro n a
      change resGroundTransferReduced H (nativeRVEvaluation h00 linear hκ hs hc B hrB hγB hΓB kind
        (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a))) =
        nativeRVEvaluation h00 linear hκ hs hc C hrC hγC hΓC kind
          (rvGroundTransferOrdinary H (GammaOrdinarySharpRingMap.sharp B (GammaOrdinaryRing.objectClass a)))
      rw [nativeRVEvaluation_gamma,rvGroundTransferOrdinary_sharp_chart,nativeRVEvaluation_gamma]
      rw [(resGroundTransferReduced H).map_mul,map_intCast (resGroundTransferReduced H),
        (resGroundTransferReduced H).map_pow,resGroundTransferReduced_torus]
      have hi := gamma_integral_parameter_independent h00 hκ hs B C hrB hγB hrC hγC kind n
        (GammaIndicators.indicatorFamily B a.support a.support_definable)
        (GammaIndicators.indicatorFamily C (gammaGroundTransferChart H a).support (gammaGroundTransferChart H a).support_definable)
        (fun _ => rfl)
      exact congrArg (fun z : ℤ => (z : RESDimensionFreeReduction.Ring C)*nativeTorusClass C^n) hi
  exact RingHom.congr_fun he x

end DiamondIntegral.Section5
