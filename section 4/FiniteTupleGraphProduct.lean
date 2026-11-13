module

public import «section 4».FiniteTupleBlocks

/-! Reorder a pair of function graphs from (x,Fx,y,Gy) to
(x,y,Fx,Gy), keeping every finite coordinate explicit. -/

@[expose] public section
set_option autoImplicit false

namespace DiamondIntegral.Section4.FiniteTupleGraphProduct
open FiniteTupleBlocks

theorem block_ext {A : Type*} (n m : ℕ) {f g : Fin (n + m) → A}
    (hh : f ∘ headIndex n m = g ∘ headIndex n m)
    (ht : f ∘ tailIndex n m = g ∘ tailIndex n m) : f = g :=
  (join_reconstruct n m f).symm.trans
    ((congrArg₂ (join n m) hh ht).trans (join_reconstruct n m g))

def graphShuffle (a b k l : ℕ) : Fin ((l + k) + (b + a)) → Fin ((l + b) + (k + a)) :=
  join (l + k) (b + a)
    (join b a
      (fun i => headIndex (l + b) (k + a) (headIndex k a i))
      (fun i => tailIndex (l + b) (k + a) (headIndex l b i)))
    (join l k
      (fun i => headIndex (l + b) (k + a) (tailIndex k a i))
      (fun i => tailIndex (l + b) (k + a) (tailIndex l b i)))

theorem graphShuffle_join {A : Type*} (a b k l : ℕ)
    (x : Fin a → A) (y : Fin k → A) (u : Fin b → A) (v : Fin l → A) :
    join (l + b) (k + a) (join k a x y) (join l b u v) ∘ graphShuffle a b k l =
      join (l + k) (b + a) (join b a x u) (join l k y v) := by
  apply block_ext (l + k) (b + a)
  · apply block_ext b a
    · funext i
      simp [graphShuffle, Function.comp_apply]
    · funext i
      simp [graphShuffle, Function.comp_apply]
  · apply block_ext l k
    · funext i
      simp [graphShuffle, Function.comp_apply]
    · funext i
      simp [graphShuffle, Function.comp_apply]

end DiamondIntegral.Section4.FiniteTupleGraphProduct
