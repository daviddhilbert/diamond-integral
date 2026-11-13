import «section 4».GammaBoundedRVPresentation
import «section 4».GammaRVIdentityIso

/-! Every intrinsic bounded Gamma chart with empty support has zero
class, regardless of its chosen partial-volume extension. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedRVEmpty
open GammaBoundedRVCharts GammaBoundedRVPresentation GammaBoundedProducts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem class_empty_support (B : Base (M := M)) {n : ℕ} (a : BoundedChart B n)
    (ha : a.support = ∅) : objectClass a = 0 := by
  let e := ofTotal B n ∅ (GammaIntegerFamilies.empty_definable_base B n) (DomainBounded.empty n)
    a.toChart.normalizedVolume a.toChart.normalizedVolume_definable
  have he : objectClass a = objectClass e := class_iso
    (GammaRVIdentityIso.sameDomainIso a.toChart e.toChart ha (by
      intro z hz
      rw [ha] at hz
      exact hz.elim))
  exact he.trans (class_empty B n a.toChart.normalizedVolume a.toChart.normalizedVolume_definable)

end DiamondIntegral.Section4.GammaBoundedRVEmpty
