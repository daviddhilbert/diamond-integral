import «section 6».GraphUniversalParameterLoci

/-! Definable source-invariance tests for complete focus graphs. This
same test applies to the ambient source and each protected source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

def focusSourceCodeCondition (A : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (j : Fin n) :
    Set (FocusMetadataIndex ι ⊕ (FocusEntryIndex n r ⊕ Fin n) → M) :=
  {z | (∀ i : Fin n,iVF (z (.inr (.inr i)))) →
    (∀ i : Fin n,¬ iLe
      (iRv (iVFAdd (z (.inr (.inl (.inl (.inl i))))) (iVFNeg (z (.inr (.inr i))))))
      (if i=j then iRv (iVFMul (z (.inl (.inl (.inr 0)))) (z (.inr (.inl (.inr 0)))))
        else z (.inl (.inr 0)))) →
    Sum.elim (fun i => z (.inl (.inl (.inl i))))
      (Sum.elim (fun i => z (.inr (.inr i))) (fun k => z (.inr (.inl (.inl (.inr k)))))) ∈ A}

theorem focusSourceCodeCondition_definable
    (A : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (hA : S.Definable LRV A) (j : Fin n) :
    S.Definable LRV (focusSourceCodeCondition A j) := by
  let Z := FocusMetadataIndex ι ⊕ (FocusEntryIndex n r ⊕ Fin n)
  let e : ι ⊕ (Fin n ⊕ Fin r) → Z := Sum.elim (fun i => .inl (.inl (.inl i)))
    (Sum.elim (fun i => .inr (.inr i)) (fun k => .inr (.inl (.inl (.inr k)))))
  have hTarget : S.Definable LRV {z : Z → M | Sum.elim (fun i => z (.inl (.inl (.inl i))))
      (Sum.elim (fun i => z (.inr (.inr i))) (fun k => z (.inr (.inl (.inl (.inr k)))))) ∈ A} := by
    convert hA.preimage_comp e using 1
    ext z
    have he : z ∘ e=Sum.elim (fun i => z (.inl (.inl (.inl i))))
        (Sum.elim (fun i => z (.inr (.inr i))) (fun k => z (.inr (.inl (.inl (.inr k)))))) := by
      funext i; rcases i with i | (i | i) <;> rfl
    change _ ∈ A ↔ z ∘ e ∈ A
    rw [he]
  have hVF : S.Definable LRV {z : Z → M | ∀ i : Fin n,iVF (z (.inr (.inr i)))} :=
    (vfRawUniverse_definable S n).preimage_comp (fun i : Fin n => (Sum.inr (Sum.inr i) : Z))
  have hClose (i : Fin n) : S.Definable LRV {z : Z → M | ¬ iLe
      (iRv (iVFAdd (z (.inr (.inl (.inl (.inl i))))) (iVFNeg (z (.inr (.inr i))))))
      (if i=j then iRv (iVFMul (z (.inl (.inl (.inr 0)))) (z (.inr (.inl (.inr 0)))))
        else z (.inl (.inr 0)))} := by
    have hInput : S.DefinableFun LRV (fun z : Z → M =>
        iRv (iVFAdd (z (.inr (.inl (.inl (.inl i))))) (iVFNeg (z (.inr (.inr i)))))) :=
      rv_scalarCode_definable (scalarSubCode_definable
        (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
    have hBound : S.DefinableFun LRV (fun z : Z → M =>
        if i=j then iRv (iVFMul (z (.inl (.inl (.inr 0)))) (z (.inr (.inl (.inr 0)))))
          else z (.inl (.inr 0))) := by
      by_cases hi : i=j
      · simpa only [if_pos hi] using rv_scalarCode_definable (scalarMulCode_definable
          (show S.DefinableFun LRV (fun z : Z → M => z (.inl (.inl (.inr 0)))) from Set.DefinableFun.proj LRV)
          (Set.DefinableFun.proj LRV))
      · simpa only [if_neg hi] using
          (show S.DefinableFun LRV (fun z : Z → M => z (.inl (.inr 0))) from Set.DefinableFun.proj LRV)
    exact (rvCode_compare_definable hInput hBound).compl
  convert hVF.compl.union ((Set.definable_iInter_of_finite hClose).compl.union hTarget) using 1
  ext z
  simp only [focusSourceCodeCondition,Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_iInter]
  constructor
  · intro h
    by_cases hV : ∀ i : Fin n,iVF (z (.inr (.inr i)))
    · by_cases hC : ∀ i : Fin n,¬ iLe
          (iRv (iVFAdd (z (.inr (.inl (.inl (.inl i))))) (iVFNeg (z (.inr (.inr i))))))
          (if i=j then iRv (iVFMul (z (.inl (.inl (.inr 0)))) (z (.inr (.inl (.inr 0)))))
            else z (.inl (.inr 0)))
      · exact Or.inr (Or.inr (h hV hC))
      · exact Or.inr (Or.inl hC)
    · exact Or.inl hV
  · intro h hV hC
    rcases h with h | h | h
    · exact False.elim (h hV)
    · exact False.elim (h hC)
    · exact h

def focusSourceInvariantParameterLocus
    (A : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (R : Set (ι ⊕ FocusEntryIndex n r → M))
    (j : Fin n) : Set (FocusMetadataIndex ι → M) :=
  graphUniversalParameterLocus (focusGraphWithMetadata R) (focusSourceCodeCondition A j)

theorem focusSourceInvariantParameterLocus_definable
    (A : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (hA : S.Definable LRV A)
    (R : Set (ι ⊕ FocusEntryIndex n r → M)) (hR : S.Definable LRV R) (j : Fin n) :
    S.Definable LRV (focusSourceInvariantParameterLocus A R j) :=
  graphUniversalParameterLocus_definable _ _ (focusGraphWithMetadata_definable R hR)
    (focusSourceCodeCondition_definable A hA j)

end DiamondIntegral.Section6
