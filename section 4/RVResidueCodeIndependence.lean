import «section 4».RVResidueIsomorphisms
import «section 4».RVUnderlyingIsomorphisms

/-! The pure-field class of any code for an actual chart domain agrees
with the chosen code. The original-base identity graph supplies the
comparison; no original-base representative is selected. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueCodeIndependence
open RVMeasuredCharts RVResidueChartCodes RVResidueIsomorphisms RVResidueCodeRelations FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem code_class_eq (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {k : ℕ} (a : Chart B k) (C D : RawCode a.domain) :
    FieldDefinableRing.objectClass (ModelResidue M) C.chart =
      FieldDefinableRing.objectClass (ModelResidue M) D.chart := by
  let F := RVUnderlyingIsomorphisms.refl a
  exact objectClass_eq hc C D
    {w | ∃ u : a.domain, w = join a.arity a.arity u.val (F.equiv u).val}
    F.graph_definable (joined_graph_biunique a.domain a.domain F.equiv)

theorem code_class_value (hc : CanonicalStructure.IsCanonical (M := M))
    [Infinite (ModelResidue M)] {B : Base (M := M)} {k : ℕ} (a : RESChart B k)
    (C : RawCode a.domain) : FieldDefinableRing.objectClass (ModelResidue M) C.chart = value hc a :=
  code_class_eq hc a.toChart C (code hc a)

end DiamondIntegral.Section4.RVResidueCodeIndependence
