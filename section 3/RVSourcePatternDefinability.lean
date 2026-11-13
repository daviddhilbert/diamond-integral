import «section 3».RVParameterPredicates
import «section 3».RVGlobalValuePatterns
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem sourceEqualityPattern_definable (p : Parameters S)
    (E : EqualityPayload (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : EqualityValuePattern E) : PresentedPredicateDefinable (rawRVUnitSpace n) S
      (equalityPatternCell E (sourceVFFixedValues p n) (sourceRVFixedParameters p) b) := by
  have he := (rvMonomial_equal_value_predicate_definable p E.left E.right).bool_pattern b.1
  have hl := PresentedPredicateDefinable.forall_finite (fun i : Fin E.leftK.size =>
    (rvMonomial_residue_predicate_definable p (E.leftK.terms i)).bool_pattern (b.2.1 i))
  have hr := PresentedPredicateDefinable.forall_finite (fun i : Fin E.rightK.size =>
    (rvMonomial_residue_predicate_definable p (E.rightK.terms i)).bool_pattern (b.2.2 i))
  exact he.and (hl.and hr)

theorem sourceLiteralPattern_definable (p : Parameters S)
    (L : RVLiteral (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : LiteralValuePattern L) : PresentedPredicateDefinable (rawRVUnitSpace n) S
      (literalPatternCell L (sourceVFFixedValues p n) (sourceRVFixedParameters p) b) := by
  cases L with
  | equality E pos => exact sourceEqualityPattern_definable p E b
  | order E pos => exact Space.definable_univ (rawRVUnitSpace n) S

theorem sourceGlobalPattern_definable (p : Parameters S)
    (D : LiteralDNF (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : RVDNFGlobalPattern D) : PresentedPredicateDefinable (rawRVUnitSpace n) S
      (fun x => ∀ L : rvDNFLiterals D, literalPatternCell L.val (sourceVFFixedValues p n) (sourceRVFixedParameters p) (b L) x) :=
  PresentedPredicateDefinable.forall_finite (fun L => sourceLiteralPattern_definable p L.val (b L))

/-- Each global value-pattern cell is definable over the same real base
as the original RV set. The guarded DNF uses only its original package. -/
theorem sourceDNFPatternCell_definable (p : Parameters S)
    (D : LiteralDNF (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n))
    (b : RVDNFGlobalPattern D) (A : Set (Fin n → M)) (hA : S.Definable LRV A)
    (hmatch : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitValues x ∈ A ↔
      PolarityDNF.holds (RVLiteral.comparison (sourceVFFixedValues p n) (sourceRVFixedParameters p)
        (fun i => (x i : CanonicalRV.RVSort M))) D) :
    (rawRVUnitSpace n).Definable S (rvDNFPatternCell D (sourceVFFixedValues p n) (sourceRVFixedParameters p) b) := by
  have hu : PresentedPredicateDefinable (rawRVUnitSpace n) S (fun x => rvUnitValues x ∈ A) :=
    rvUnitSpace_predicate_definable S _ (fun z => z ∈ A) hA (fun _ => Iff.rfl)
  apply (hu.and (sourceGlobalPattern_definable p D b)).congr
  intro x
  change (rvUnitValues x ∈ A ∧ _) ↔ (_ ∧ _)
  rw [hmatch x]
end DiamondIntegral.Section3
