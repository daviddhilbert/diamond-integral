import «section 5».Completed18TwoOrders
import IntegrationSection6.ContractionOrderComparison

/-! The completed [18] Section 5 proofs instantiate the precise scoped
two-order registry used throughout its Section 6 kernel proof. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem completed_section5_input {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : SpecialTransformations.Section3.Saturated M κ) :
    IntegrationInACVF.Section6.Section5TwoOrderInputAll hκ hs := by
  intro B hr hκ' h00 δ hδ hδ1
  exact completed_two_order_input hκ' hs h00 B hr δ hδ hδ1

end DiamondIntegral.Section5
