import «section 6».RowGammaTransitionImages
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».GammaCoreParameterLoci

/-! (Row-form version for Remark 6.20, replacing `GammaCoreParameterLoci`.)
Core-row compatibility is a complete first-order parameter test: entries
on the true branch whose targets agree off the active coordinate and on all
output labels transfer row membership. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s qR : ℕ}

def gammaCoreJointGraphRow
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (coreTag : Fin s) : Set (Fin p ⊕ GammaTransitionEntryRow n r s qR → M) :=
  {z | z ∈ gammaTransitionJointGraphRow R W ∧
    z (.inr (.inr (.inl (.inr coreTag)))) = (branchTag (M := M) true).val}

theorem gammaCoreJointGraph_definable_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) (coreTag : Fin s) :
    S.Definable LRV (gammaCoreJointGraphRow R W coreTag) :=
  (gammaTransitionJointGraph_definable_row R W hR hW).inter
    ((Set.DefinableFun.proj LRV).ofPred_eq (branchTag_definable S true))

def gammaCoreTransitionCodeConditionRow
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) (j : Fin n) :
    Set (Fin p ⊕ (GammaTransitionEntryRow n r s qR ⊕ GammaTransitionEntryRow n r s qR) → M) :=
  {z | (∀ i : Fin n, i ≠ j →
      z (.inr (.inl (.inr (.inl (.inl i))))) = z (.inr (.inr (.inr (.inl (.inl i)))))) →
    z ∈ gammaTransitionCodeConditionRow W}

theorem gammaCoreTransitionCodeCondition_definable_row
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) (hW : S.Definable LRV W) (j : Fin n) :
    S.Definable LRV (gammaCoreTransitionCodeConditionRow (s := s) W j) := by
  let Z := Fin p ⊕ (GammaTransitionEntryRow n r s qR ⊕ GammaTransitionEntryRow n r s qR)
  have hOther (i : {i : Fin n // i ≠ j}) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inr (.inl (.inl i.val))))) = z (.inr (.inr (.inr (.inl (.inl i.val)))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hΓ := gammaTransitionCodeCondition_definable_row (s := s) W hW
  convert (Set.definable_iInter_of_finite hOther).compl.union hΓ using 1
  ext z
  simp only [gammaCoreTransitionCodeConditionRow, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
    Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hAll : ∀ i : {i : Fin n // i ≠ j},
        z (.inr (.inl (.inr (.inl (.inl i.val))))) = z (.inr (.inr (.inr (.inl (.inl i.val)))))
    · exact Or.inr (h (fun i hi => hAll ⟨i, hi⟩))
    · exact Or.inl hAll
  · intro h hAll
    rcases h with h | h
    · exact False.elim (h (fun i => hAll i.val i.property))
    · exact h

def gammaCoreConstantParameterLocusRow
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (j : Fin n) (coreTag : Fin s) : Set (Fin p → M) :=
  binaryGraphConditionLocus (gammaCoreJointGraphRow R W coreTag)
    (gammaCoreTransitionCodeConditionRow W j)

theorem gammaCoreConstantParameterLocus_definable_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) (j : Fin n) (coreTag : Fin s) :
    S.Definable LRV (gammaCoreConstantParameterLocusRow R W j coreTag) :=
  binaryGraphConditionLocus_definable _ _ (gammaCoreJointGraph_definable_row R W hR hW coreTag)
    (gammaCoreTransitionCodeCondition_definable_row W hW j)

end DiamondIntegral.Section6
