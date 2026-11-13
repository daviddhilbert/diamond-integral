import «section 4».FiniteTupleBlocks
import Mathlib.Data.Set.Function

/-! Cartesian products of actual tuple bijections, without changing
the project's prefix/suffix convention. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.TupleProductBijections
open FiniteTupleBlocks
variable {K F : Type*} {a b n m : ℕ}

def domain (A : Set (Fin a → K)) (B : Set (Fin b → K)) : Set (Fin (b + a) → K) :=
  {x | x ∘ headIndex b a ∈ A ∧ x ∘ tailIndex b a ∈ B}

def map (f : (Fin a → K) → (Fin n → F)) (g : (Fin b → K) → (Fin m → F))
    (x : Fin (b + a) → K) : Fin (m + n) → F :=
  join m n (f (x ∘ headIndex b a)) (g (x ∘ tailIndex b a))

theorem map_head (f : (Fin a → K) → (Fin n → F)) (g : (Fin b → K) → (Fin m → F))
    (x : Fin (b + a) → K) : map f g x ∘ headIndex m n = f (x ∘ headIndex b a) :=
  funext (join_head _ _ _ _)

theorem map_tail (f : (Fin a → K) → (Fin n → F)) (g : (Fin b → K) → (Fin m → F))
    (x : Fin (b + a) → K) : map f g x ∘ tailIndex m n = g (x ∘ tailIndex b a) :=
  funext (join_tail _ _ _ _)

theorem bijOn {A : Set (Fin a → K)} {B : Set (Fin b → K)}
    {S : Set (Fin n → F)} {T : Set (Fin m → F)}
    (f : (Fin a → K) → (Fin n → F)) (g : (Fin b → K) → (Fin m → F))
    (hf : Set.BijOn f A S) (hg : Set.BijOn g B T) :
    Set.BijOn (map f g) (domain A B) (domain S T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(map_head f g x).symm ▸ hf.mapsTo hx.1,
      (map_tail f g x).symm ▸ hg.mapsTo hx.2⟩
  · intro x hx y hy he
    have hh : f (x ∘ headIndex b a) = f (y ∘ headIndex b a) :=
      (map_head f g x).symm.trans
        ((congrArg (fun z => z ∘ headIndex m n) he).trans (map_head f g y))
    have ht : g (x ∘ tailIndex b a) = g (y ∘ tailIndex b a) :=
      (map_tail f g x).symm.trans
        ((congrArg (fun z => z ∘ tailIndex m n) he).trans (map_tail f g y))
    have hh' := hf.injOn hx.1 hy.1 hh
    have ht' := hg.injOn hx.2 hy.2 ht
    exact (join_reconstruct b a x).symm.trans
      ((congrArg₂ (join b a) hh' ht').trans (join_reconstruct b a y))
  · intro z hz
    obtain ⟨x, hx, hfx⟩ := hf.surjOn hz.1
    obtain ⟨y, hy, hgy⟩ := hg.surjOn hz.2
    let w := join b a x y
    have hh : w ∘ headIndex b a = x := funext (join_head _ _ _ _)
    have ht : w ∘ tailIndex b a = y := funext (join_tail _ _ _ _)
    refine ⟨w, ⟨hh.symm ▸ hx, ht.symm ▸ hy⟩, ?_⟩
    change join m n (f (w ∘ headIndex b a)) (g (w ∘ tailIndex b a)) = z
    rw [hh, ht, hfx, hgy]
    exact join_reconstruct m n z

end DiamondIntegral.Section4.TupleProductBijections
