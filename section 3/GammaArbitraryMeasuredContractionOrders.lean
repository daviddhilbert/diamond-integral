import «section 3».GammaCommonHeadMeasuredOrders
import IntegrationSection6.ContractionOrderBridge

/-! Arbitrary-order independence for complete Gamma densities follows
from same-order comparison, common-head induction and the proved
selected first-two exchange. No kernel statement is used as input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaSelected_all_order_measured_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (n : ℕ) :
    GammaSelectedMeasuredOrderIndependent hc B C hBC n := by
  induction n with
  | zero =>
    intro a d A hA ρ hfin ω σ υ T E hT hE
    have hOrder : υ = σ := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      have hυ := (υ i).isLt
      have hσ := (σ i).isLt
      omega
    subst υ
    exact gammaSelected_standard_same_order_values C hBC hv hg δ hδ hδ1 A hA ρ hfin ω T E hT hE
  | succ n ih =>
    intro a d A hA ρ hfin ω σ υ T E hT hE
    by_cases h0 : σ 0 = υ 0
    · exact gammaSelected_common_head_measured_orders C hBC hv hg hGenerated δ hδ hδ1 ih
        A hA ρ hfin ω σ υ h0 T E hT hE
    · let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
      obtain ⟨π,hπ0,hπ1⟩ := exists_contraction_bridge_order σ υ h0
      obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr
        hGenerated hBC A hA π
      obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr
        hGenerated hBC A hA ((swapFirstTwo n).trans π)
      have hLeft := gammaSelected_common_head_measured_orders C hBC hv hg hGenerated δ hδ hδ1 ih
        A hA ρ hfin ω σ π hπ0.symm T D hT hD
      have hFirst : ((swapFirstTwo n).trans π) 0 = υ 0 := by
        change π (swapFirstTwo n 0) = υ 0
        rw [swapFirstTwo_zero]
        exact hπ1
      have hRight := gammaSelected_common_head_measured_orders C hBC hv hg hGenerated δ hδ hδ1 ih
        A hA ρ hfin ω ((swapFirstTwo n).trans π) υ hFirst F E hF hE
      have hMiddle := gammaSelected_standard_first_two_values C hBC hv hg δ hδ hδ1 hNames hGenerated
        A hA ρ hfin ω D F hD hF
      exact hLeft.trans (hMiddle.trans hRight)

end DiamondIntegral.Section3
