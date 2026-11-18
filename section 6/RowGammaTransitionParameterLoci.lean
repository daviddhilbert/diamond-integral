import «section 6».RowForms
import «section 6».GammaTransitionParameterLoci

/-! (Row-form version for Remark 6.20, replacing `GammaTransitionParameterLoci`.)
A complete first-order test that a row form is constant on equal output RV
labels of a transition. Entries are a source, its target and an RV tuple;
the pair condition says that equal target labels transfer membership of the
tuple in the row of the first source to the row of the second. Quantifying
over all tuples, this is equality of rows. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s qR : ℕ}

abbrev GammaTransitionEntryRow (n r s qR : ℕ) :=
  (Fin n ⊕ Fin r) ⊕ ((Fin n ⊕ Fin s) ⊕ Fin qR)

/-- Entries: a transition pair together with a tuple in the marked row graph of the source. -/
def gammaTransitionJointGraphRow
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) :
    Set (Fin p ⊕ GammaTransitionEntryRow n r s qR → M) :=
  {z | Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
      (fun i => z (.inr (.inr (.inl i))))) ∈ R ∧
    Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
      (fun i => z (.inr (.inr (.inr i))))) ∈ W}

theorem gammaTransitionJointGraph_definable_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) (hR : S.Definable LRV R) (hW : S.Definable LRV W) :
    S.Definable LRV (gammaTransitionJointGraphRow R W) := by
  have h₁ : S.DefinableMap LRV (fun z : Fin p ⊕ GammaTransitionEntryRow n r s qR → M =>
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
        (fun i => z (.inr (.inr (.inl i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have h₂ : S.DefinableMap LRV (fun z : Fin p ⊕ GammaTransitionEntryRow n r s qR → M =>
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
        (fun i => z (.inr (.inr (.inr i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  exact (hR.preimage_map h₁).inter (hW.preimage_map h₂)

/-- The pair condition: equal target labels put the first entry's tuple in the
marked row graph of the second source. -/
def gammaTransitionCodeConditionRow
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) :
    Set (Fin p ⊕ (GammaTransitionEntryRow n r s qR ⊕ GammaTransitionEntryRow n r s qR) → M) :=
  {z | (∀ j : Fin s, z (.inr (.inl (.inr (.inl (.inr j))))) = z (.inr (.inr (.inr (.inl (.inr j)))))) →
    Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inr (.inl i))))
      (fun i => z (.inr (.inl (.inr (.inr i)))))) ∈ W}

theorem gammaTransitionCodeCondition_definable_row
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) (hW : S.Definable LRV W) :
    S.Definable LRV (gammaTransitionCodeConditionRow (s := s) W) := by
  let Z := Fin p ⊕ (GammaTransitionEntryRow n r s qR ⊕ GammaTransitionEntryRow n r s qR)
  have hTags (j : Fin s) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inr (.inl (.inr j))))) = z (.inr (.inr (.inr (.inl (.inr j)))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have h₂ : S.DefinableMap LRV (fun z : Z → M => Sum.elim (z ∘ Sum.inl)
      (Sum.elim (fun i => z (.inr (.inr (.inl i)))) (fun i => z (.inr (.inl (.inr (.inr i))))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  convert (Set.definable_iInter_of_finite hTags).compl.union (hW.preimage_map h₂) using 1
  ext z
  simp only [gammaTransitionCodeConditionRow, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
    Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [imp_iff_not_or]
  exact Iff.rfl

def gammaTransitionConstantParameterLocusRow
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M)) : Set (Fin p → M) :=
  binaryGraphConditionLocus (gammaTransitionJointGraphRow R W) (gammaTransitionCodeConditionRow (s := s) W)

theorem gammaTransitionConstantParameterLocus_definable_row
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ Fin qR) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) :
    S.Definable LRV (gammaTransitionConstantParameterLocusRow R W) :=
  binaryGraphConditionLocus_definable _ _ (gammaTransitionJointGraph_definable_row R W hR hW)
    (gammaTransitionCodeCondition_definable_row W hW)

end DiamondIntegral.Section6
