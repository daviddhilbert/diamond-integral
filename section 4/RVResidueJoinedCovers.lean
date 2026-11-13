import «section 4».RVResidueScaledCovers

/-! Scaled-coordinate covers respect the manuscript's prefix/suffix
tuple convention, including arbitrary graph and product arities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueJoinedCovers
open RVResidueScaledCovers FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def pieceJoin {α β : Type} {n m : ℕ} (p : Piece (M := M) α n)
    (q : Piece (M := M) β m) : Piece (M := M) (α ⊕ β) (m + n) where
  guard := {x | x ∘ Sum.inl ∈ p.guard ∧ x ∘ Sum.inr ∈ q.guard}
  definable := (p.definable.preimage_comp Sum.inl).inter (q.definable.preimage_comp Sum.inr)
  scale := join m n p.scale q.scale
  coord := join m n (Sum.inl ∘ p.coord) (Sum.inr ∘ q.coord)

theorem pieceJoin_value {α β : Type} {n m : ℕ} (p : Piece (M := M) α n)
    (q : Piece (M := M) β m) (x : α ⊕ β → ModelResidue M) :
    (pieceJoin p q).value x = join m n (p.value (x ∘ Sum.inl)) (q.value (x ∘ Sum.inr)) := by
  have hh : (pieceJoin p q).value x ∘ headIndex m n = p.value (x ∘ Sum.inl) := by
    funext i
    simp only [Piece.value, pieceJoin, residueScale, Function.comp_apply, join_head]
  have ht : (pieceJoin p q).value x ∘ tailIndex m n = q.value (x ∘ Sum.inr) := by
    funext i
    simp only [Piece.value, pieceJoin, residueScale, Function.comp_apply, join_tail]
  exact (join_reconstruct m n ((pieceJoin p q).value x)).symm.trans (by rw [hh, ht])

def coverJoin {α β : Type} {n m : ℕ} {D : Set (α → ModelResidue M)}
    {E : Set (β → ModelResidue M)}
    {decode : (α → ModelResidue M) → (Fin n → CanonicalRV.RVSort M)}
    {decode' : (β → ModelResidue M) → (Fin m → CanonicalRV.RVSort M)}
    (C : Cover D decode) (C' : Cover E decode') :
    Cover {x : α ⊕ β → ModelResidue M | x ∘ Sum.inl ∈ D ∧ x ∘ Sum.inr ∈ E}
      (fun x => join m n (decode (x ∘ Sum.inl)) (decode' (x ∘ Sum.inr))) where
  Index := C.Index × C'.Index
  finite := by letI := C.finite; letI := C'.finite; infer_instance
  piece i := pieceJoin (C.piece i.1) (C'.piece i.2)
  covers x hx := by
    obtain ⟨i, hi⟩ := C.covers _ hx.1
    obtain ⟨j, hj⟩ := C'.covers _ hx.2
    exact ⟨(i, j), hi, hj⟩
  agrees i x hx hi := by
    rw [C.agrees i.1 _ hx.1 hi.1, C'.agrees i.2 _ hx.2 hi.2, pieceJoin_value]

end DiamondIntegral.Section4.RVResidueJoinedCovers
