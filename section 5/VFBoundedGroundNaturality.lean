import «section 5».NativeRVRetractionGroundNaturality
import «section 5».VFNormalizedMapExt

/-! The intrinsic bounded VF integral commutes with actual sorted
parameter substitution. Only the precise Section 3 lifting inputs at
the two displayed bases are used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable (H : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
  DefinableOverBase B sn D → DefinableOverBase C sn D)
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hrB : Cardinal.mk B.real < κ) (hγB : Cardinal.mk B.gamma < κ) (hΓB : Section2.NontrivialDefinableGamma B)
variable (hrC : Cardinal.mk C.real < κ) (hγC : Cardinal.mk C.gamma < κ) (hΓC : Section2.NontrivialDefinableGamma C)

theorem originalBaseVFBoundedValue_parameter_naturality
    (I : OriginalBaseUnmeasuredLiftInput hc B) (J : OriginalBaseUnmeasuredLiftInput hc C)
    (x : GammaGroundVFGrothendieckRing hc B) :
    resGroundTransferReduced H (originalBaseVFBoundedValue h00 linear hκ hs hrB hγB hΓB I x) =
      originalBaseVFBoundedValue h00 linear hκ hs hrC hγC hΓC J (sortedTransferVFRing H x) := by
  have he : (resGroundTransferReduced H).comp (originalBaseVFBoundedValue h00 linear hκ hs hrB hγB hΓB I) =
      (originalBaseVFBoundedValue h00 linear hκ hs hrC hγC hΓC J).comp (sortedTransferVFRing H) := by
    apply vfNormalizedMap_ext I
    intro k U
    change resGroundTransferReduced H (originalBaseVFBoundedValue h00 linear hκ hs hrB hγB hΓB I
      (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U)))) =
      originalBaseVFBoundedValue h00 linear hκ hs hrC hγC hΓC J
        (sortedTransferVFRing H (of (gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))))
    rw [originalBaseVFBoundedValue_lift_class,sortedTransferVFRing_lift,originalBaseVFBoundedValue_lift_class]
    exact nativeGroundRVEvaluation_parameter_naturality H h00 linear hκ hs hrB hγB hΓB hrC hγC hΓC .bounded U
  exact RingHom.congr_fun he x

end DiamondIntegral.Section5
