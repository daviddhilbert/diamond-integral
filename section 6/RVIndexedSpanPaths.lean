import «section 6».RVTupleSpanGeometry
import Mathlib.Logic.Relation

/-! Finite paths through tuples selected from a fixed coordinate pool.
Every vertex generates exactly the same RV algebraic closure. Steps are
one-coordinate replacements or coordinate permutations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))

def RVIndexedSpanStep (S : Set M) {m n : ℕ} (pool : Fin m → RVInfinity M)
    (a b : Fin n → Fin m) : Prop :=
  ((∃ i p, b = Function.update a i p) ∨ (∃ e : Equiv.Perm (Fin n), b = a ∘ e)) ∧
    rvTupleClosure hc hex S (pool ∘ a) = rvTupleClosure hc hex S (pool ∘ b)

theorem RVIndexedSpanStep.reindex (S : Set M) {m n : ℕ} (pool : Fin m → RVInfinity M)
    (a : Fin n → Fin m) (e : Equiv.Perm (Fin n)) :
    RVIndexedSpanStep hc hex S pool a (a ∘ e) := by
  exact ⟨Or.inr ⟨e,rfl⟩,(rvTupleClosure_reindex hc hex S (pool ∘ a) e).symm⟩

theorem RVIndexedSpanStep.snoc (S : Set M) {m n : ℕ} (pool : Fin m → RVInfinity M)
    {a b : Fin n → Fin m} (p : Fin m)
    (h : RVIndexedSpanStep hc hex (insert (pool p).val S) pool a b) :
    RVIndexedSpanStep hc hex S pool (Fin.snoc a p) (Fin.snoc b p) := by
  constructor
  · rcases h.1 with ⟨i,q,rfl⟩ | ⟨e,rfl⟩
    · exact Or.inl ⟨i.castSucc,q,by rw [Fin.snoc_update]⟩
    · exact Or.inr ⟨finPermFixLast e,(snoc_comp_finPermFixLast a p e).symm⟩
  · rw [comp_snoc,comp_snoc,rvTupleClosure_snoc,rvTupleClosure_snoc]
    exact h.2

theorem rvIndexedSpanPath_snoc (S : Set M) {m n : ℕ} (pool : Fin m → RVInfinity M)
    {a b : Fin n → Fin m} (p : Fin m)
    (h : Relation.ReflTransGen (RVIndexedSpanStep hc hex (insert (pool p).val S) pool) a b) :
    Relation.ReflTransGen (RVIndexedSpanStep hc hex S pool) (Fin.snoc a p) (Fin.snoc b p) := by
  induction h with
  | refl => exact .refl
  | tail _ hStep ih => exact ih.tail (RVIndexedSpanStep.snoc hc hex S pool p hStep)

theorem exists_rvIndexedSpanPath (S : Set M) {m n : ℕ} (pool : Fin m → RVInfinity M)
    (a b : Fin n → Fin m)
    (he : rvTupleClosure hc hex S (pool ∘ a) = rvTupleClosure hc hex S (pool ∘ b)) :
    Relation.ReflTransGen (RVIndexedSpanStep hc hex S pool) a b := by
  induction n generalizing S with
  | zero =>
    have h : a = b := Subsingleton.elim _ _
    subst b
    exact .refl
  | succ n ih =>
    let N := rvAlgebraicMatroid hc hex S
    obtain ⟨i,j,hPivot⟩ := exists_interalgebraic_tuple_pivot N (Nat.zero_lt_succ n)
      (pool ∘ a) (pool ∘ b)
      (by change Set.range (pool ∘ a) ⊆ Set.univ; exact Set.subset_univ _)
      (by change Set.range (pool ∘ b) ⊆ Set.univ; exact Set.subset_univ _) he
    let c := Function.update a i (b j)
    have hC : rvTupleClosure hc hex S (pool ∘ c) = rvTupleClosure hc hex S (pool ∘ a) := by
      rw [Function.comp_update]
      exact hPivot
    have hAC : RVIndexedSpanStep hc hex S pool a c := ⟨Or.inl ⟨i,b j,rfl⟩,hC.symm⟩
    let σ := Equiv.swap i (Fin.last n)
    let τ := Equiv.swap j (Fin.last n)
    let d := c ∘ σ
    let e := b ∘ τ
    have hd : d (Fin.last n) = b j := by
      change Function.update a i (b j) (Equiv.swap i (Fin.last n) (Fin.last n)) = b j
      rw [Equiv.swap_apply_right,Function.update_self]
    have heLast : e (Fin.last n) = b j := Equiv.swap_apply_right j (Fin.last n) ▸ rfl
    have hSnocD : Fin.snoc (Fin.init d) (b j) = d := by
      simpa only [hd] using Fin.snoc_init_self d
    have hSnocE : Fin.snoc (Fin.init e) (b j) = e := by
      simpa only [heLast] using Fin.snoc_init_self e
    have hDE : rvTupleClosure hc hex S (pool ∘ d) = rvTupleClosure hc hex S (pool ∘ e) :=
      (rvTupleClosure_reindex hc hex S (pool ∘ c) σ).trans
        (hC.trans (he.trans (rvTupleClosure_reindex hc hex S (pool ∘ b) τ).symm))
    have hPref : rvTupleClosure hc hex (insert (pool (b j)).val S) (pool ∘ Fin.init d) =
        rvTupleClosure hc hex (insert (pool (b j)).val S) (pool ∘ Fin.init e) := by
      rw [← hSnocD,← hSnocE,comp_snoc,comp_snoc,rvTupleClosure_snoc,rvTupleClosure_snoc] at hDE
      exact hDE
    have hTail := rvIndexedSpanPath_snoc hc hex S pool (b j)
      (ih (insert (pool (b j)).val S) (Fin.init d) (Fin.init e) hPref)
    rw [hSnocD,hSnocE] at hTail
    have hBack : e ∘ τ.symm = b := by
      funext k
      exact congrArg b (τ.apply_symm_apply k)
    have hEB := RVIndexedSpanStep.reindex hc hex S pool e τ.symm
    rw [hBack] at hEB
    exact (Relation.ReflTransGen.single hAC).trans
      ((Relation.ReflTransGen.single (RVIndexedSpanStep.reindex hc hex S pool c σ)).trans
        (hTail.trans (Relation.ReflTransGen.single hEB)))

end DiamondIntegral.Section6
