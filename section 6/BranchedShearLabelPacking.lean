import «section 6».FiniteDefinableChoicePartitions

/-! Finite chart families with different output arities share one RV
code. The code retains old labels, one leading term and a block for every
local output; unused blocks are filled with the nonzero unit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ}

abbrev BranchedLabelIndex (r : ℕ) {k : ℕ} (arity : Fin k → ℕ) :=
  Fin r ⊕ (Fin 1 ⊕ Σ i : Fin k,Fin (arity i))

def packedBranchArity (r : ℕ) {k : ℕ} (arity : Fin k → ℕ) : ℕ := Fintype.card (BranchedLabelIndex r arity)

def packedBranchEquiv (r : ℕ) {k : ℕ} (arity : Fin k → ℕ) :
    BranchedLabelIndex r arity ≃ Fin (packedBranchArity r arity) := Fintype.equivFin _

def packedBranchOld (r : ℕ) {k : ℕ} (arity : Fin k → ℕ) (j : Fin r) := packedBranchEquiv r arity (.inl j)
def packedBranchLeading (r : ℕ) {k : ℕ} (arity : Fin k → ℕ) := packedBranchEquiv r arity (.inr (.inl 0))
def packedBranchSlot (r : ℕ) {k : ℕ} (arity : Fin k → ℕ) (i : Fin k) (j : Fin (arity i)) :=
  packedBranchEquiv r arity (.inr (.inr ⟨i,j⟩))

def packedBranchEncode (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (arity i) → RVInfinity M) :
    Fin (packedBranchArity r arity) → RVInfinity M := fun z =>
  match (packedBranchEquiv r arity).symm z with
  | .inl j => u j
  | .inr (.inl _) => v (leading i)
  | .inr (.inr ⟨j,l⟩) => if h : j=i then v (Fin.cast (congrArg arity h) l) else 1

def packedBranchDecode (arity : Fin k → ℕ) (i : Fin k)
    (v : Fin (packedBranchArity r arity) → RVInfinity M) : Fin (arity i) → RVInfinity M :=
  fun j => v (packedBranchSlot r arity i j)

theorem packedBranchOld_injective (arity : Fin k → ℕ) : Function.Injective (packedBranchOld r arity) := by
  intro i j h
  exact Sum.inl_injective ((packedBranchEquiv r arity).injective h)

theorem packedBranchEncode_old (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (arity i) → RVInfinity M) (j : Fin r) :
    packedBranchEncode arity leading i u v (packedBranchOld r arity j)=u j := by
  simp only [packedBranchEncode,packedBranchOld,Equiv.symm_apply_apply]

theorem packedBranchEncode_leading (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (arity i) → RVInfinity M) :
    packedBranchEncode arity leading i u v (packedBranchLeading r arity)=v (leading i) := by
  simp only [packedBranchEncode,packedBranchLeading,Equiv.symm_apply_apply]

theorem packedBranchDecode_encode (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (arity i) → RVInfinity M) :
    packedBranchDecode arity i (packedBranchEncode arity leading i u v)=v := by
  funext j
  simp [packedBranchDecode,packedBranchSlot,packedBranchEncode]

theorem packedBranchEncode_injective (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) : Function.Injective (packedBranchEncode arity leading i u) := by
  intro v w h
  have he := congrArg (packedBranchDecode arity i) h
  simpa only [packedBranchDecode_encode] using he

theorem packedBranchEncode_nonzero (arity : Fin k → ℕ) (leading : ∀ i,Fin (arity i)) (i : Fin k)
    (u : Fin r → RVInfinity M) (v : Fin (arity i) → RVInfinity M)
    (hu : ∀ j,(u j).val ≠ iRVZero) (hv : ∀ j,(v j).val ≠ iRVZero) :
    ∀ j,(packedBranchEncode arity leading i u v j).val ≠ iRVZero := by
  intro j
  unfold packedBranchEncode
  split
  · exact hu _
  · exact hv _
  · split
    · exact hv _
    · intro h
      exact (one_ne_zero : (1 : RVInfinity M) ≠ 0)
        (Subtype.ext (h.trans RVOperations.zero_val.symm))

end DiamondIntegral.Section6
