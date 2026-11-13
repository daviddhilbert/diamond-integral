module

public import «section 4».FiniteTupleRotation

@[expose] public section
set_option autoImplicit false

namespace DiamondIntegral.Section4.FiniteTupleBlocks

def blockSwap (n m : ℕ) : Fin (n + m) ≃ Fin (m + n) :=
  (finCongr (Nat.add_comm n m)).trans
    ((finAddFlip : Fin (m + n) ≃ Fin (n + m)).trans (finCongr (Nat.add_comm n m)))

theorem blockSwap_head (n m : ℕ) (i : Fin m) :
    blockSwap n m (headIndex n m i) = tailIndex m n i := by
  have hc : finCongr (Nat.add_comm n m) (headIndex n m i) = Fin.castAdd n i := by
    apply Fin.ext
    exact headIndex_val n m i
  change finCongr (Nat.add_comm n m) (finAddFlip (finCongr (Nat.add_comm n m) (headIndex n m i))) = _
  rw [hc, finAddFlip_apply_castAdd]
  apply Fin.ext
  exact (tailIndex_val m n i).symm

theorem blockSwap_tail (n m : ℕ) (i : Fin n) :
    blockSwap n m (tailIndex n m i) = headIndex m n i := by
  have hc : finCongr (Nat.add_comm n m) (tailIndex n m i) = Fin.natAdd m i := by
    apply Fin.ext
    exact tailIndex_val n m i
  change finCongr (Nat.add_comm n m) (finAddFlip (finCongr (Nat.add_comm n m) (tailIndex n m i))) = _
  rw [hc, finAddFlip_apply_natAdd]
  apply Fin.ext
  exact (headIndex_val m n i).symm

theorem join_blockSwap {α : Type*} (n m : ℕ) (u : Fin m → α) (y : Fin n → α) :
    (join m n y u) ∘ blockSwap n m = join n m u y := by
  have hh : ((join m n y u) ∘ blockSwap n m) ∘ headIndex n m = u := by
    funext i
    change join m n y u (blockSwap n m (headIndex n m i)) = u i
    rw [blockSwap_head, join_tail]
  have ht : ((join m n y u) ∘ blockSwap n m) ∘ tailIndex n m = y := by
    funext i
    change join m n y u (blockSwap n m (tailIndex n m i)) = y i
    rw [blockSwap_tail, join_head]
  calc
    _ = join n m (((join m n y u) ∘ blockSwap n m) ∘ headIndex n m)
        (((join m n y u) ∘ blockSwap n m) ∘ tailIndex n m) := (join_reconstruct n m _).symm
    _ = _ := by rw [hh, ht]

end DiamondIntegral.Section4.FiniteTupleBlocks
