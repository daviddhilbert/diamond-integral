import «section 5».NativeWeakRVObjects
import «section 5».NativePullbackRVPresentation
import «section 5».NativeVFPullbackValues

/-! An arbitrary RV-pullback, including all zero-coordinate strata, has
one actual RV[<=n] presentation with finite labels. No positive
cancellation or new parameter is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

def nativePullbackWeakRVObject
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) : NativeWeakRVObject hc B n where
  arity := n+r
  domain := (nativeMixedFullKeyMap A).image
  volume := nativePullbackRVLabels A
  finite := finite_native_RV_labels_of_finite_lift _ _
    ((gammaGroundFiniteRVFibres_iff (nativePullbackLiftBijection A hpull) hκ hs h00 hr).mp hf)

def nativePullbackWeakRVObject_lift_bijection
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) (hpull : IsRVPullback A.carrier)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) :
    GammaGroundBijection A (nativeWeakRVObjectLift (nativePullbackWeakRVObject hκ hs h00 hr A hpull hf)) :=
  nativePullbackLiftBijection A hpull

end DiamondIntegral.Section5
