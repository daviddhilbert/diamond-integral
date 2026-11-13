import «section 3».RVUnitSpace
import «section 3».RVParameterTerms
import «section 3».RVRawPredicates
import «section 3».PresentedPredicateLogic
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

theorem rvMonomial_residue_predicate_definable (p : Parameters S)
    (T : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    PresentedPredicateDefinable (rawRVUnitSpace n) S (fun x => ValuedModelMap.inK
      (T.rawEval (sourceVFFixedValues p n) (sourceRVFixedParameters p) (fun i => (x i : CanonicalRV.RVSort M)))) := by
  let f := parameterTermFunction p (rvMonomialParameterTerm p T)
  apply rvUnitSpace_predicate_definable S _ (fun z => iUnits (f z) ∨ f z = iRVZero)
    (rvRaw_inK_definable f (parameterTermFunction_definable p _))
  intro x
  have ht := rvMonomialParameterTerm_realize p T (fun i => (x i : CanonicalRV.RVSort M))
  change f (rvUnitValues x) = _ at ht
  rw [ht]
  simp only [ValuedModelMap.inK,Subtype.ext_iff,ValuedModelMap.zeroRV]

theorem rvMonomial_equal_value_predicate_definable (p : Parameters S)
    (T U : Monomial (VFSlot p.sorts (fun _ : Fin n => .rv)) (RVParameterSlot p.sorts) (Fin n)) :
    PresentedPredicateDefinable (rawRVUnitSpace n) S (fun x =>
      RVOperations.absoluteHom (T.rawEval (sourceVFFixedValues p n) (sourceRVFixedParameters p) (fun i => (x i : CanonicalRV.RVSort M))) =
      RVOperations.absoluteHom (U.rawEval (sourceVFFixedValues p n) (sourceRVFixedParameters p) (fun i => (x i : CanonicalRV.RVSort M)))) := by
  let f := parameterTermFunction p (rvMonomialParameterTerm p T)
  let g := parameterTermFunction p (rvMonomialParameterTerm p U)
  apply rvUnitSpace_predicate_definable S _ (fun z => iLe (f z) (g z) ∧ iLe (g z) (f z))
    (rvRaw_same_value_definable f g (parameterTermFunction_definable p _) (parameterTermFunction_definable p _))
  intro x
  have ht := rvMonomialParameterTerm_realize p T (fun i => (x i : CanonicalRV.RVSort M))
  have hu := rvMonomialParameterTerm_realize p U (fun i => (x i : CanonicalRV.RVSort M))
  change f (rvUnitValues x) = _ at ht
  change g (rvUnitValues x) = _ at hu
  rw [ht,hu,rvLe_iff_absolute,rvLe_iff_absolute]
  exact ⟨fun h => by rw [h]; exact ⟨le_rfl,le_rfl⟩,fun h => le_antisymm h.2 h.1⟩
end DiamondIntegral.Section3
