import «section 3».ResidueScaledEquality
import Section3.GuardedRVLiterals
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {I R V M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem residuePolynomial_rawEval_inK (P : KPolynomial I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M)
    (hP : P.Domain a r y) : ValuedModelMap.inK (P.rawEval a r y) := by
  rw [KPolynomial.rawEval,KPolynomial.rvSum_eq_lift_sum Values.presentationValuation Values.presentation_compatible
    _ (fun i => (hP i).2)]
  exact ResidueRVAlgebra.residueRVHom_inK _ _ _

/-- A guarded equality separates into a Gamma value comparison and flat
residue data. Both zero and nonzero residue-polynomial values are retained. -/
theorem guarded_equality_value_split (E : EqualityPayload I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M)
    (hD : RVLiteral.Domain a r y (.equality E true))
    (hL : E.left.rawEval a r y ≠ 0) (hR : E.right.rawEval a r y ≠ 0) :
    E.left.rawEval a r y * E.leftK.rawEval a r y = E.right.rawEval a r y * E.rightK.rawEval a r y ↔
      if RVOperations.absoluteHom (E.left.rawEval a r y) = RVOperations.absoluteHom (E.right.rawEval a r y)
      then E.leftK.rawEval a r y = (E.right.rawEval a r y / E.left.rawEval a r y) * E.rightK.rawEval a r y
      else E.leftK.rawEval a r y = 0 ∧ E.rightK.rawEval a r y = 0 := by
  by_cases he : RVOperations.absoluteHom (E.left.rawEval a r y) = RVOperations.absoluteHom (E.right.rawEval a r y)
  · rw [if_pos he]
    exact residue_scaled_equality_ratio _ _ _ _ hL
  · rw [if_neg he]
    exact residue_scaled_equality_distinct_values _ _ _ _ hL hR
      (residuePolynomial_rawEval_inK E.leftK a r y hD.2.1)
      (residuePolynomial_rawEval_inK E.rightK a r y hD.2.2.2) he

theorem guarded_equality_ratio_inK (E : EqualityPayload I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : V → CanonicalRV.RVSort M)
    (hL : E.left.rawEval a r y ≠ 0)
    (he : RVOperations.absoluteHom (E.left.rawEval a r y) = RVOperations.absoluteHom (E.right.rawEval a r y)) :
    ValuedModelMap.inK (E.right.rawEval a r y / E.left.rawEval a r y) :=
  residue_ratio_of_equal_values _ _ hL he
end DiamondIntegral.Section3
