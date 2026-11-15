import «section 5».NativeGeometricPadding
import «section 3».GammaGroundRealExtensions
import «section 3».GammaGroundCarrierBijections

/-! Actual native RV objects extend real parameters with their literal
domains and maps unchanged. Affine padding over the original ground has
the expected raw affine-power value over every displayed fibre base.
No injectivity of a parameter-extension map is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {T : Set M} (h : B.real ⊆ T)

def nativeRVObjectMonoReal {k : ℕ} (U : GammaGroundRVObject hc B k) :
    GammaGroundRVObject hc (⟨T,B.gamma⟩ : Base (M := M)) k where
  arity := U.arity
  domain := U.domain.monoReal h
  volume := (U.volume.monoReal h).corestrict (fun _ => Set.mem_univ _)
  finite := by
    intro t
    exact U.finite ⟨t.val,Set.mem_univ _⟩
  nonzero := U.nonzero

def nativeRVObjectMonoReal_product {k l : ℕ} (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    GammaGroundBijection (nativeRVObjectMonoReal h (U.product V)).domain
      ((nativeRVObjectMonoReal h U).product (nativeRVObjectMonoReal h V)).domain :=
  GammaGroundBijection.ofCarrierEq rfl

def nativeRVObjectMonoReal_affine :
    GammaGroundBijection (nativeRVObjectMonoReal h (nativeAffineRVObject hc B)).domain
      (nativeAffineRVObject hc (⟨T,B.gamma⟩ : Base (M := M))).domain :=
  GammaGroundBijection.ofCarrierEq rfl

def nativeRVObjectMonoReal_unit :
    GammaGroundBijection (nativeRVObjectMonoReal h (GammaGroundRVObject.unit hc B)).domain
      (GammaGroundRVObject.unit hc (⟨T,B.gamma⟩ : Base (M := M))).domain :=
  GammaGroundBijection.ofCarrierEq rfl

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk T < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma (⟨T,B.gamma⟩ : Base (M := M)))

theorem nativeAffineRVPower_monoReal_raw_value (kind : EulerKind) (r : ℕ) :
    nativeGroundRVEvaluation h00 linear hκ hs hc (⟨T,B.gamma⟩ : Base (M := M)) hr hγ hΓ kind
      (ordinaryClass (nativeRVObjectMonoReal h (nativeAffineRVPower hc B r))) =
        RESAffineLocalization.dimensionFreeAffine (⟨T,B.gamma⟩ : Base (M := M)) ^ r := by
  induction r with
  | zero =>
    have he := nativeGroundRVEvaluation_bijection h00 linear hκ hs hc (⟨T,B.gamma⟩ : Base (M := M)) hr hγ hΓ kind
      _ _ (nativeRVObjectMonoReal_unit h)
    exact he.trans (nativeAffineRVPower_raw_value (B := (⟨T,B.gamma⟩ : Base (M := M))) h00 linear hκ hs hr hγ hΓ kind 0)
  | succ r ih =>
    have he := nativeGroundRVEvaluation_bijection h00 linear hκ hs hc (⟨T,B.gamma⟩ : Base (M := M)) hr hγ hΓ kind
      _ _ (nativeRVObjectMonoReal_product h (nativeAffineRVPower hc B r) (nativeAffineRVObject hc B))
    refine he.trans ?_
    rw [nativeGroundRVEvaluation_product,ih]
    have ha := nativeGroundRVEvaluation_bijection h00 linear hκ hs hc (⟨T,B.gamma⟩ : Base (M := M)) hr hγ hΓ kind
      _ _ (nativeRVObjectMonoReal_affine h)
    rw [ha,nativeAffineRVObject_raw_value,pow_succ]

end DiamondIntegral.Section5
