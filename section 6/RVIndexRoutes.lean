import «section 6».RVFiniteVolumeLoci

/-! Finite coordinate routes contain only indices and permutations, so
the routes themselves introduce no RV parameters. The pointwise span
path supplies such a route with algebraicity at every visited vertex. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6

inductive RVIndexRoute (n m : ℕ) : (Fin n → Fin m) → (Fin n → Fin m) → Type where
  | identity (a : Fin n → Fin m) : RVIndexRoute n m a a
  | coordinate (a : Fin n → Fin m) (i : Fin n) (p : Fin m) {b : Fin n → Fin m}
      (tail : RVIndexRoute n m (Function.update a i p) b) : RVIndexRoute n m a b
  | reindex (a : Fin n → Fin m) (e : Equiv.Perm (Fin n)) {b : Fin n → Fin m}
      (tail : RVIndexRoute n m (a ∘ e) b) : RVIndexRoute n m a b

def RVIndexRoute.All {n m : ℕ} {a b : Fin n → Fin m} (P : (Fin n → Fin m) → Prop) :
    RVIndexRoute n m a b → Prop
  | .identity a => P a
  | .coordinate a _ _ T => P a ∧ T.All P
  | .reindex a _ T => P a ∧ T.All P

def RVIndexRoute.vertices {n m : ℕ} {a b : Fin n → Fin m} :
    RVIndexRoute n m a b → Finset (Fin n → Fin m)
  | .identity a => {a}
  | .coordinate a _ _ T => insert a T.vertices
  | .reindex a _ T => insert a T.vertices

theorem RVIndexRoute.all_iff {n m : ℕ} {a b : Fin n → Fin m}
    (T : RVIndexRoute n m a b) (P : (Fin n → Fin m) → Prop) :
    T.All P ↔ ∀ v ∈ T.vertices, P v := by
  induction T <;> simp_all only [All,vertices,Finset.mem_singleton,Finset.mem_insert,
    forall_eq,forall_eq_or_imp]

theorem RVIndexRoute.all_target {n m : ℕ} {a b : Fin n → Fin m}
    (T : RVIndexRoute n m a b) {P : (Fin n → Fin m) → Prop} (hT : T.All P) : P b := by
  induction T with
  | identity => exact hT
  | coordinate a i p T ih => exact ih hT.2
  | reindex a e T ih => exact ih hT.2

def RVIndexRoute.comp {n m : ℕ} {a b c : Fin n → Fin m} :
    RVIndexRoute n m a b → RVIndexRoute n m b c → RVIndexRoute n m a c
  | .identity _,H => H
  | .coordinate a i p T,H => .coordinate a i p (T.comp H)
  | .reindex a e T,H => .reindex a e (T.comp H)

theorem RVIndexRoute.all_comp {n m : ℕ} {a b c : Fin n → Fin m}
    (T : RVIndexRoute n m a b) (H : RVIndexRoute n m b c)
    {P : (Fin n → Fin m) → Prop} (hT : T.All P) (hH : H.All P) : (T.comp H).All P := by
  induction T with
  | identity => exact hH
  | coordinate a i p T ih => exact ⟨hT.1,ih H hT.2 hH⟩
  | reindex a e T ih => exact ⟨hT.1,ih H hT.2 hH⟩

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_rvIndexRoute_of_span_path (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) (S : Set M) {m n : ℕ} (pool : Fin m → RVInfinity M)
    {a b : Fin n → Fin m} (h : Relation.ReflTransGen (RVIndexedSpanStep hc hex S pool) a b) :
    ∃ T : RVIndexRoute n m a b,
      T.All (fun v => rvTupleClosure hc hex S (pool ∘ v) = rvTupleClosure hc hex S (pool ∘ a)) := by
  induction h with
  | refl => exact ⟨.identity _,rfl⟩
  | @tail b c h hStep ih =>
    obtain ⟨T,hT⟩ := ih
    have hB := T.all_target hT
    have hC := hStep.2.symm.trans hB
    rcases hStep.1 with ⟨i,p,rfl⟩ | ⟨e,rfl⟩
    · let H : RVIndexRoute n m b (Function.update b i p) := .coordinate b i p (.identity _)
      exact ⟨T.comp H,T.all_comp H hT ⟨hB,hC⟩⟩
    · let H : RVIndexRoute n m b (b ∘ e) := .reindex b e (.identity _)
      exact ⟨T.comp H,T.all_comp H hT ⟨hB,hC⟩⟩

end DiamondIntegral.Section6
