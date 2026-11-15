import «section 5».OriginalBaseVFIntegral
import «section 5».NormalizedVFBoundedValues

/-! The exact Section 3 lifting/kernel input computes every positive
RV[<=k] representative of a VF object at its unchanged parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
variable (H : OriginalBaseUnmeasuredLiftInput hc B)

theorem originalBaseVFBoundedValue_of_weak_lift_bijection
    (A : GammaGroundFiniteVFObject hc B) {k : ℕ} (U : NativeWeakRVObject hc B k)
    (e : GammaGroundBijection A.domain (nativeWeakRVObjectLift U)) :
    originalBaseVFBoundedValue h00 linear hκ.le hs hr hγ hΓ H (nativeVFClass A) =
      nativeRVSetValue h00 linear hκ.le hs hc B hr hγ hΓ .bounded U.domain :=
  normalizedVFBoundedValue_of_weak_lift_bijection h00 linear hκ.le hs hr hγ hΓ
    (originalBaseVFBoundedValue h00 linear hκ.le hs hr hγ hΓ H)
    (originalBaseVFBoundedValue_lift_class h00 linear hκ.le hs hr hγ hΓ H) A U e

theorem originalBaseVFBoundedValue_positive_presentation (A : GammaGroundFiniteVFObject hc B) :
    ∃ k : ℕ,∃ U : NativeWeakRVObject hc B k,
      Nonempty (GammaGroundBijection A.domain (nativeWeakRVObjectLift U)) ∧
        originalBaseVFBoundedValue h00 linear hκ.le hs hr hγ hΓ H (nativeVFClass A) =
          nativeRVSetValue h00 linear hκ.le hs hc B hr hγ hΓ .bounded U.domain := by
  obtain ⟨k,U,⟨e⟩⟩ := native_arbitrary_weak_rv_lift_exists hκ hs h00 hr A
  exact ⟨k,U,⟨e⟩,originalBaseVFBoundedValue_of_weak_lift_bijection h00 linear hκ hs hr hγ hΓ H A U e⟩

end DiamondIntegral.Section5
