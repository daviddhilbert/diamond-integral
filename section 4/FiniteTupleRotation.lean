module

public import «section 4».FiniteTupleBlocks
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section
set_option autoImplicit false

namespace DiamondIntegral.Section4.FiniteTupleBlocks

theorem headIndex_val (n m : ℕ) (i : Fin m) : (headIndex n m i).val = i.val := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg Nat.succ (ih j)

theorem tailIndex_val (n m : ℕ) (i : Fin n) : (tailIndex n m i).val = m + i.val := by
  induction m with
  | zero => simp [tailIndex]
  | succ m ih =>
    change (tailIndex n m i).val + 1 = m + 1 + i.val
    omega

def outputToLast (n : ℕ) : Fin (n + 1) ≃ Fin (1 + n) :=
  (finRotate (n + 1)).symm.trans (finCongr (Nat.add_comm n 1))

theorem outputToLast_zero (n : ℕ) : outputToLast n 0 = tailIndex 1 n 0 := by
  have h : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (finRotate (n + 1)).symm_apply_eq.mpr finRotate_last.symm
  apply Fin.ext
  simp [outputToLast, h, tailIndex_val]

theorem outputToLast_succ (n : ℕ) (i : Fin n) : outputToLast n i.succ = headIndex 1 n i := by
  have h : (finRotate (n + 1)).symm i.succ = i.castSucc :=
    (finRotate (n + 1)).symm_apply_eq.mpr (finRotate_of_lt i.isLt).symm
  apply Fin.ext
  simp [outputToLast, h, headIndex_val]

theorem join_rotate {α : Type*} (n : ℕ) (u : Fin n → α) (a : α) :
    (join 1 n u ![a]) ∘ outputToLast n = Fin.cons a u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change join 1 n u ![a] (outputToLast n 0) = a
    rw [outputToLast_zero, join_tail]
    rfl
  · change join 1 n u ![a] (outputToLast n j.succ) = u j
    rw [outputToLast_succ, join_head]

end DiamondIntegral.Section4.FiniteTupleBlocks
