import «section 6».BranchedShearTemplateRows

/-! Retention and nonzero output labels are first-order admissibility
conditions for every whole indicator row, with exact typed bridges. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

theorem rawRVZero_constant_definable {ι : Type} : S.DefinableFun LRV (fun _ : ι → M => iRVZero) :=
  (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
    (show S.DefinableMap LRV (fun _ : ι → M => (Fin.elim0 : Fin 0 → M)) from fun i => i.elim0)

namespace BranchedShearChartTemplate

def retentionCode (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin (r+s) ⊕ Fin (n+1) → M) :=
  {z | ∀ i : Fin r,z (.inl (Fin.natAdd r (T.labels i)))=z (.inl (Fin.castAdd s i))}

theorem retentionCode_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.retentionCode := by
  have hEach (i : Fin r) : S.Definable LRV {z : Fin (r+s) ⊕ Fin (n+1) → M |
      z (.inl (Fin.natAdd r (T.labels i)))=z (.inl (Fin.castAdd s i))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  convert Set.definable_iInter_of_finite hEach using 1
  ext z
  simp only [retentionCode,Set.mem_setOf_eq,Set.mem_iInter]

def nonzeroCode (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin (r+s) ⊕ Fin (n+1) → M) :=
  {z | ∀ i : Fin s,z (.inl (Fin.natAdd r i)) ≠ iRVZero}

theorem nonzeroCode_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.nonzeroCode := by
  have hEach (i : Fin s) : S.Definable LRV {z : Fin (r+s) ⊕ Fin (n+1) → M |
      z (.inl (Fin.natAdd r i)) ≠ iRVZero} :=
    ((Set.DefinableFun.proj LRV).ofPred_eq rawRVZero_constant_definable).compl
  convert Set.definable_iInter_of_finite hEach using 1
  ext z
  simp only [nonzeroCode,Set.mem_setOf_eq,Set.mem_iInter]

def retainedGood (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin p → M) :=
  rawRowSubsetParameterLocus T.oneCode {z | z ∘ Sum.inr ∈ T.retentionCode}

def nonzeroGood (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin p → M) :=
  rawRowSubsetParameterLocus T.oneCode {z | z ∘ Sum.inr ∈ T.nonzeroCode}

theorem retainedGood_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.retainedGood :=
  rawRowSubsetParameterLocus_definable _ _ T.oneCode_definable (T.retentionCode_definable.preimage_comp Sum.inr)

theorem nonzeroGood_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.nonzeroGood :=
  rawRowSubsetParameterLocus_definable _ _ T.oneCode_definable (T.nonzeroCode_definable.preimage_comp Sum.inr)

theorem retainedGood_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) :
    a ∈ T.retainedGood ↔ ∀ w x,T.indicator.value a ha w x 0=1 →
      (w ∘ Fin.natAdd r) ∘ T.labels=w ∘ Fin.castAdd s := by
  rw [retainedGood,T.oneCode_subset_iff a ha T.retentionCode]
  constructor
  · intro h w x hx
    funext i
    apply Subtype.ext
    exact h w x hx i
  · intro h w x hx i
    exact congrArg Subtype.val (congrFun (h w x hx) i)

theorem nonzeroGood_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) :
    a ∈ T.nonzeroGood ↔ ∀ w x,T.indicator.value a ha w x 0=1 →
      ∀ i : Fin s,(w (Fin.natAdd r i)).val ≠ iRVZero := by
  rw [nonzeroGood,T.oneCode_subset_iff a ha T.nonzeroCode]
  rfl

end BranchedShearChartTemplate
end DiamondIntegral.Section6
