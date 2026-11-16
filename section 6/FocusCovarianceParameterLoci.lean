import «section 6».FocusGraphIndependence
import «section 6».PointwiseFocusCovariance

/-! The erased-coordinate covariance condition is first-order in
the complete focus graph, named coefficient and a proper Gamma code.
All parameters remain in the original template prefix. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

abbrev FocusEntryIndex (n r : ℕ) := (Fin n ⊕ Fin r) ⊕ Fin 1
abbrev FocusMetadataIndex (ι : Type) := (ι ⊕ Fin 1) ⊕ Fin 1

def focusGraphWithMetadata (R : Set (ι ⊕ FocusEntryIndex n r → M)) :
    Set (FocusMetadataIndex ι ⊕ FocusEntryIndex n r → M) :=
  {z | Sum.elim (fun i => z (.inl (.inl (.inl i)))) (z ∘ Sum.inr) ∈ R}

theorem focusGraphWithMetadata_definable
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (focusGraphWithMetadata R) := by
  let e : ι ⊕ FocusEntryIndex n r → FocusMetadataIndex ι ⊕ FocusEntryIndex n r :=
    Sum.elim (fun i => .inl (.inl (.inl i))) Sum.inr
  convert hR.preimage_comp e using 1
  ext z
  have he : z ∘ e=Sum.elim (fun i => z (.inl (.inl (.inl i)))) (z ∘ Sum.inr) := by
    funext i; cases i <;> rfl
  change _ ∈ R ↔ z ∘ e ∈ R
  rw [he]

def focusCovarianceCodeCondition (ι : Type) (j : Fin n) :
    Set (FocusMetadataIndex ι ⊕ (FocusEntryIndex n r ⊕ FocusEntryIndex n r) → M) :=
  {z | (∀ k : Fin r,z (.inr (.inl (.inl (.inr k))))=z (.inr (.inr (.inl (.inr k))))) →
    (∀ i : Fin n,i ≠ j → ¬ iLe
      (iRv (iVFAdd (z (.inr (.inl (.inl (.inl i))))) (iVFNeg (z (.inr (.inr (.inl (.inl i))))))))
      (z (.inl (.inr 0)))) →
    ¬ iLe (iRv (iVFAdd (z (.inr (.inl (.inr 0)))) (iVFNeg (z (.inr (.inr (.inr 0)))))))
      (iRv (iVFMul (z (.inl (.inl (.inr 0)))) (z (.inr (.inl (.inr 0))))))}

theorem focusCovarianceCodeCondition_definable (j : Fin n) :
    S.Definable LRV (focusCovarianceCodeCondition (M := M) ι (r := r) j) := by
  let Z := FocusMetadataIndex ι ⊕ (FocusEntryIndex n r ⊕ FocusEntryIndex n r)
  have hRV (k : Fin r) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inl (.inr k))))=z (.inr (.inr (.inl (.inr k))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hClose (i : {i : Fin n // i ≠ j}) : S.Definable LRV {z : Z → M | ¬ iLe
      (iRv (iVFAdd (z (.inr (.inl (.inl (.inl i.val))))) (iVFNeg (z (.inr (.inr (.inl (.inl i.val))))))))
      (z (.inl (.inr 0)))} :=
    (rvCode_compare_definable (rv_scalarCode_definable
      (scalarSubCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)))
        (Set.DefinableFun.proj LRV)).compl
  have hCut : S.Definable LRV {z : Z → M |
      ¬ iLe (iRv (iVFAdd (z (.inr (.inl (.inr 0)))) (iVFNeg (z (.inr (.inr (.inr 0)))))))
        (iRv (iVFMul (z (.inl (.inl (.inr 0)))) (z (.inr (.inl (.inr 0))))))} :=
    (rvCode_compare_definable (rv_scalarCode_definable
      (scalarSubCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)))
        (rv_scalarCode_definable (scalarMulCode_definable
          (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)))).compl
  convert (Set.definable_iInter_of_finite hRV).compl.union
    ((Set.definable_iInter_of_finite hClose).compl.union hCut) using 1
  ext z
  simp only [focusCovarianceCodeCondition,Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_iInter]
  constructor
  · intro h
    by_cases hTags : ∀ k : Fin r,z (.inr (.inl (.inl (.inr k))))=z (.inr (.inr (.inl (.inr k))))
    · by_cases hOther : ∀ i : {i : Fin n // i ≠ j},¬ iLe
          (iRv (iVFAdd (z (.inr (.inl (.inl (.inl i.val))))) (iVFNeg (z (.inr (.inr (.inl (.inl i.val))))))))
          (z (.inl (.inr 0)))
      · exact Or.inr (Or.inr (h hTags (fun i hi => hOther ⟨i,hi⟩)))
      · exact Or.inr (Or.inl hOther)
    · exact Or.inl hTags
  · intro h hTags hOther
    rcases h with h | h | h
    · exact False.elim (h hTags)
    · exact False.elim (h (fun i => hOther i.val i.property))
    · exact h

def focusErasedCovarianceParameterLocus
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (j : Fin n) : Set (FocusMetadataIndex ι → M) :=
  binaryGraphConditionLocus (focusGraphWithMetadata R) (focusCovarianceCodeCondition ι j)

theorem focusErasedCovarianceParameterLocus_definable
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (hR : S.Definable LRV R) (j : Fin n) :
    S.Definable LRV (focusErasedCovarianceParameterLocus R j) :=
  binaryGraphConditionLocus_definable _ _ (focusGraphWithMetadata_definable R hR)
    (focusCovarianceCodeCondition_definable j)

end DiamondIntegral.Section6
