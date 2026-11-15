import «section 5».NativeArbitraryVFPullbackPreparation
import «section 5».NativeWeakLiftValues

/-! Every finite-RV-fibre VF object has one actual RV[<=k] lift
presentation, including mixed-dimensional fibres and zero strata. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem native_arbitrary_weak_rv_lift_exists
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundFiniteVFObject hc B) :
    ∃ k : ℕ,∃ U : NativeWeakRVObject hc B k,Nonempty (GammaGroundBijection A.domain (nativeWeakRVObjectLift U)) := by
  obtain ⟨l,Y,⟨e⟩,hpull⟩ := native_arbitrary_vf_pullback_preparation hκ hs h00 hr A.domain
  have hf := (gammaGroundFiniteRVFibres_iff e hκ.le hs h00 hr).mp A.finite
  let U := nativePullbackWeakRVObject hκ.le hs h00 hr Y hpull hf
  exact ⟨A.vfArity,U,⟨(nativePullbackWeakRVObject_lift_bijection hκ.le hs h00 hr Y hpull hf).comp e⟩⟩

variable {G : GammaGroundContext M}

theorem native_arbitrary_weak_rv_integral_presentation
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc) (A : GammaGroundFiniteVFObject hc G.base) :
    ∃ k : ℕ,∃ U : NativeWeakRVObject hc G.base k,
      Nonempty (GammaGroundBijection A.domain (nativeWeakRVObjectLift U)) ∧
        nativeVFBoundedValue linear H (nativeVFClass A) =
          nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
            G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded U.domain := by
  obtain ⟨k,U,⟨e⟩⟩ := native_arbitrary_weak_rv_lift_exists G.uncountable G.saturated G.model00 G.small_real A
  exact ⟨k,U,⟨e⟩,nativeVFBoundedValue_of_weak_lift_bijection linear H A U e⟩

end DiamondIntegral.Section5
