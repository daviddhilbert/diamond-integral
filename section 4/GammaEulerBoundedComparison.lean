import «section 4».GammaEulerEvaluation
import «section 4».GammaBoundedRVMaps
import «section 4».GammaBoundedFamilies

/-! Direct ordinary Gamma evaluation is independent of Euler choice on
bounded charts. This uses bounded Euler comparison, without the
canonical-structure premise needed by the bounded profile-range bridge. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaEulerEvaluation
open GammaBoundedFamilies GammaIndicators
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem bounded_independent_kind (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) {R : Type*} [CommRing R] (t : R) :
    (evaluation h00 linear hκ hs B hr hγ hΓ k t).comp (GammaBoundedRVMaps.forget B) =
      (evaluation h00 linear hκ hs B hr hγ hΓ l t).comp (GammaBoundedRVMaps.forget B) := by
  apply GammaBoundedRVPresentation.hom_ext B
  intro n a
  change evaluation h00 linear hκ hs B hr hγ hΓ k t
    (GammaBoundedRVMaps.forget B (GammaBoundedRVPresentation.objectClass a)) =
      evaluation h00 linear hκ hs B hr hγ hΓ l t
        (GammaBoundedRVMaps.forget B (GammaBoundedRVPresentation.objectClass a))
  rw [GammaBoundedRVMaps.forget_class, evaluation_class, evaluation_class]
  obtain ⟨β, hβ⟩ := a.domain_bounded
  have hb : BoxSupported β⁻¹ β (indicatorFamily B a.support a.support_definable).val := by
    intro z hz i
    have hi : z ∈ a.support := by
      by_contra hn
      exact hz (by simp [indicatorFamily, hn])
    exact hβ z hi i
  exact congrArg (fun z : ℤ => (z : R) * t ^ n)
    (integrateAll_bounded_comparison h00 hκ hs B hr hγ k l n
      (indicatorFamily B a.support a.support_definable) β⁻¹ β hb)

end DiamondIntegral.Section4.GammaEulerEvaluation
