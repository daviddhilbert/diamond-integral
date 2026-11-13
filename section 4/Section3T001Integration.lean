import «section 4».Section3CoefficientPairTransport

/-! Actual end-to-end transport of the finalized Section 3 tensor kernel
presentations. Both formerly replaceable T001 interfaces are constructed
from compiled upstream proofs, with all original hypotheses retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.Section3T001Integration
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinaryTransport (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    Section3PresentationAudit.OrdinaryTransport hc B where
  source := Section3TensorRingEquivalences.ordinary hc B
  target := Section3RVRingEquivalences.ordinary hc B
  comparison := Section3TensorComparisonSquares.ordinary hc B
  pair := Section3CoefficientPairTransport.ordinary

def measuredTransport (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    Section3PresentationAudit.MeasuredTransport hc B where
  source := Section3TensorRingEquivalences.measured hc B
  target := Section3RVRingEquivalences.measured hc B
  comparison := Section3TensorComparisonSquares.measured hc B
  pair := Section3CoefficientPairTransport.measured

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
  (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (hΓ : Section2.NontrivialDefinableGamma B)
include hc hκ hs h00 hr hγ hΓ

theorem ordinary : ApprovedT001Presentation.Ordinary B :=
  Section3PresentationAudit.ordinary hκ hs h00 hr hγ hΓ (ordinaryTransport hc B)
theorem measured : ApprovedT001Presentation.Measured B :=
  Section3PresentationAudit.measured hκ hs h00 hr hγ hΓ (measuredTransport hc B)

end DiamondIntegral.Section4.Section3T001Integration
