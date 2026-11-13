module

public import Mathlib.Data.Fin.Tuple.Basic

/-! Prefix/suffix coordinates, arranged so that adding a prefix coordinate
is definitionally `Fin.cons`. This avoids changing coordinate order when
iterating unary integration. -/

@[expose] public section
set_option autoImplicit false

namespace DiamondIntegral.Section4.FiniteTupleBlocks

def headIndex (n : ℕ) : (m : ℕ) → Fin m → Fin (n + m)
  | 0 => Fin.elim0
  | m + 1 => Fin.cases 0 (fun i => (headIndex n m i).succ)

def tailIndex (n : ℕ) : (m : ℕ) → Fin n → Fin (n + m)
  | 0 => id
  | m + 1 => fun i => (tailIndex n m i).succ

def join {α : Type*} (n : ℕ) : (m : ℕ) → (Fin m → α) → (Fin n → α) → (Fin (n + m) → α)
  | 0, _, y => y
  | m + 1, u, y => Fin.cons (u 0) (join n m (Fin.tail u) y)

theorem headIndex_injective (n m : ℕ) : Function.Injective (headIndex n m) := by
  induction m with
  | zero => exact fun i => Fin.elim0 i
  | succ m ih =>
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    · intro _; rfl
    · intro h; exact (Fin.succ_ne_zero _ h.symm).elim
    · intro h; exact (Fin.succ_ne_zero _ h).elim
    · intro h; exact congrArg Fin.succ (ih (Fin.succ_injective _ h))

theorem tailIndex_injective (n m : ℕ) : Function.Injective (tailIndex n m) := by
  induction m with
  | zero => exact Function.injective_id
  | succ m ih =>
    intro i j h
    exact ih (Fin.succ_injective _ h)

@[simp] theorem join_head {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) (i : Fin m) :
    join n m u y (headIndex n m i) = u i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    exact Fin.cases rfl (fun j => ih (Fin.tail u) j) i

@[simp] theorem join_tail {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) (i : Fin n) :
    join n m u y (tailIndex n m i) = y i := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih (Fin.tail u)

theorem join_reconstruct {α : Type*} (n m : ℕ) (z : Fin (n + m) → α) :
    join n m (z ∘ headIndex n m) (z ∘ tailIndex n m) = z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (Fin.tail z)) j) i

end DiamondIntegral.Section4.FiniteTupleBlocks
