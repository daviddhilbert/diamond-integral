import «section 4».GammaRVUniversal
import «section 4».GammaTupleMaps
import «section 4».RVSharpCharts

/-! Equal Gamma domains and equal partial weights give an actual
original-base RV-lifted identity isomorphism. This justifies replacing
extensions and using normalized volumes in the restricted presentation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRVIdentityIso
open GammaWeightedCharts GammaRVChartPresentation GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sameDomainIso {B : Base (M := M)} {n : ℕ} (a b : Chart B n)
    (hs : a.support = b.support) (hv : ∀ z ∈ a.support, a.volume z = b.volume z) : RVVolumeIso a b where
  map := id
  graph_definable := GammaTupleMaps.graph_definable B a.support a.support_definable id
    (fun i => projection_definable B i)
  bijective :=
    ⟨(by intro z hz; change z ∈ b.support; rwa [← hs]),
      (by intro x hx y hy h; exact h),
      (by intro z hz; exact ⟨z, hs.symm ▸ hz, rfl⟩)⟩
  volume_eq := by
    intro z hz
    change a.volume z = b.volume z * (∏ i, z i) / (∏ i, z i)
    simpa only [mul_div_cancel_right] using hv z hz
  lift := id
  lift_definable := by
    have h := RVSharpCharts.identity_graph_definable B (sharp a.support) (sharp_definable a.support a.support_definable)
    convert h using 1
    ext w
    change (_ ∧ _ = _) ↔ (_ ∧ _ = _)
    exact and_congr_right (fun _ => eq_comm)
  lift_bijective :=
    ⟨(by intro z hz; change z ∈ sharp b.support; rwa [← hs]),
      (by intro x hx y hy h; exact h),
      (by intro z hz; exact ⟨z, hs.symm ▸ hz, rfl⟩)⟩
  contraction := fun _ _ => rfl

theorem class_eq_on_domain {B : Base (M := M)} {n : ℕ} (a b : Chart B n)
    (hs : a.support = b.support) (hv : ∀ z ∈ a.support, a.volume z = b.volume z) :
    objectClass a = objectClass b := class_iso (sameDomainIso a b hs hv)

def normalizedIso {B : Base (M := M)} {n : ℕ} (a : Chart B n) :
    RVVolumeIso a (GammaChartOperations.ofTotal B n a.support a.support_definable
      a.normalizedVolume a.normalizedVolume_definable) :=
  sameDomainIso _ _ rfl (fun z hz => (a.normalizedVolume_on z hz).symm)

theorem class_normalized {B : Base (M := M)} {n : ℕ} (a : Chart B n) :
    objectClass a = objectClass (GammaChartOperations.ofTotal B n a.support a.support_definable
      a.normalizedVolume a.normalizedVolume_definable) := class_iso (normalizedIso a)

end DiamondIntegral.Section4.GammaRVIdentityIso
