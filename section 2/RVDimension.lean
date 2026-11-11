import «section 2».FiniteSets

/-!
# RV dimension and the approved empty-set convention

For nonempty definable sets the dimension is the least target arity of an
original-base definable finite-to-one map into nonzero RV. Empty sets have
dimension −∞. RV^0 is the singleton empty tuple.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language Set
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvInputValues {m : ℕ} (t : Fin m → RVInfinity M) : Fin m → M := fun i => (t i).val

def rvTargetValues {k : ℕ} (t : Fin k → RV M) : Fin k → M := fun i => (t i).val.val

def rvMapGraph {m k : ℕ} (U : Set (Fin m → RVInfinity M)) (f : U → Fin k → RV M) :
    Set (Fin (m + k) → M) :=
  {z | ∃ u : U, rvInputValues u.val = z ∘ finSumFinEquiv ∘ Sum.inl ∧
    rvTargetValues (f u) = z ∘ finSumFinEquiv ∘ Sum.inr}

/-- The exact original-base finite-to-one map condition in the manuscript. -/
def RVHasFiniteMap {m : ℕ} (S : Set M) (U : Set (Fin m → RVInfinity M)) (k : ℕ) : Prop :=
  ∃ f : U → Fin k → RV M, (∀ t, {u | f u = t}.Finite) ∧
    DefinableOver S (fun _ => .rv) (rvMapGraph U f)

noncomputable def rvDimension {m : ℕ} (S : Set M) (U : Set (Fin m → RVInfinity M)) :
    WithBot ℕ := by
  classical
  exact if U.Nonempty then (sInf {k | RVHasFiniteMap S U k} : ℕ) else ⊥

@[simp] theorem rvDimension_empty (S : Set M) (m : ℕ) :
    rvDimension S (∅ : Set (Fin m → RVInfinity M)) = ⊥ := by
  simp [rvDimension]

@[simp] theorem rvDimension_eq_bot_iff {m : ℕ} (S : Set M)
    (U : Set (Fin m → RVInfinity M)) : rvDimension S U = ⊥ ↔ U = ∅ := by
  classical
  by_cases hU : U.Nonempty
  · constructor
    · intro hd
      rw [rvDimension, ite_eq_left hU] at hd
      change ((sInf {k | RVHasFiniteMap S U k} : ℕ) : WithBot ℕ) = ⊥ at hd
      exact (WithBot.coe_ne_bot hd).elim
    · intro he
      exact (Set.nonempty_iff_ne_empty.mp hU he).elim
  · have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    simp [he]

theorem rvDimension_empty_lt (S : Set M) (m k : ℕ) :
    rvDimension S (∅ : Set (Fin m → RVInfinity M)) < (k : WithBot ℕ) := by
  simp

private noncomputable def rvCode {m : ℕ} (t : Fin m → M) (j : Fin (m * 2)) : M :=
  nonzeroRVCode (t (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

private theorem rvCode_definable (S : Set M) (m : ℕ) :
    S.DefinableMap LRV (rvCode (M := M) (m := m)) := by
  intro j
  exact nonzeroRVCode_definable S (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

private def rawRVGraph {m k : ℕ} (V : Set (Fin m → M))
    (F : (Fin m → M) → Fin k → M) : Set (Fin (m + k) → M) :=
  {z | z ∘ finSumFinEquiv ∘ Sum.inl ∈ V ∧
    F (z ∘ finSumFinEquiv ∘ Sum.inl) = z ∘ finSumFinEquiv ∘ Sum.inr}

omit hM in
private theorem rawRVGraph_definable {m k : ℕ} (S : Set M) (V : Set (Fin m → M))
    (hV : S.Definable LRV V) (F : (Fin m → M) → Fin k → M)
    (hF : S.DefinableMap LRV F) : S.Definable LRV (rawRVGraph V F) := by
  have hg : S.Definable LRV {z : Fin (m + k) → M |
      F (z ∘ finSumFinEquiv ∘ Sum.inl) = z ∘ finSumFinEquiv ∘ Sum.inr} := by
    have h (j : Fin k) := (hF j).preimage_comp
      (fun i : Option (Fin m) => i.elim (finSumFinEquiv (.inr j))
        (fun l => finSumFinEquiv (.inl l)))
    convert Set.definable_iInter_of_finite h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Function.tupleGraph]
    exact ⟨fun he j => congrFun he j, fun he => funext (fun j => he j)⟩
  exact (hV.preimage_comp (fun j => finSumFinEquiv (.inl j))).inter hg

/-- Definability guarantees that the set of eligible target arities is
nonempty. The constructed code is injective and uses nonzero RV entries. -/
theorem rv_finite_map_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) {m : ℕ} (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    RVHasFiniteMap S U (m * 2) := by
  classical
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  let := hΓ
  have hne := r023_distinct_tags h00 v hv
  let g (u : U) (j : Fin (m * 2)) : RV M :=
    ⟨⟨rvCode (rvInputValues u.val) j,
      (nonzeroRVCode_proper _ (u.val (finProdFinEquiv.symm j).1).property _).1⟩,
      fun he => (nonzeroRVCode_proper _ (u.val (finProdFinEquiv.symm j).1).property _).2
        (congrArg Subtype.val he)⟩
  have hinj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply nonzeroRVCode_injective hne
    funext k
    have he := congrArg (fun t : RV M => t.val.val)
      (congrFun hab (finProdFinEquiv (j, k)))
    simpa only [g, rvCode, rvInputValues, Equiv.symm_apply_apply] using he
  refine ⟨g, ?_, ?_⟩
  · intro t
    exact (show Set.Subsingleton {u | g u = t} from
      fun a ha b hb => hinj (ha.trans hb.symm)).finite
  · apply raw_definableOver_sorted hc
    · have he : rvMapGraph U g = rawRVGraph (rvInputValues '' U) rvCode := by
        ext z
        constructor
        · rintro ⟨u, hu, hf⟩
          refine ⟨⟨u.val, u.property, hu⟩, ?_⟩
          change rvCode (z ∘ finSumFinEquiv ∘ Sum.inl) = _
          rw [← hu]
          exact hf
        · rintro ⟨⟨u, hu, hv⟩, hf⟩
          refine ⟨⟨u, hu⟩, hv, ?_⟩
          change rvCode (rvInputValues u) = _
          rw [hv]
          exact hf
      rw [he]
      exact rawRVGraph_definable S _ hU.raw_definable _ (rvCode_definable S m)
    · rintro z ⟨u, hx, hy⟩ i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      cases j with
      | inl j =>
        change iRV (z (finSumFinEquiv (.inl j)))
        have he := congrFun hx j
        change (u.val j).val = z (finSumFinEquiv (.inl j)) at he
        rw [← he]
        exact (u.val j).property
      | inr j =>
        change iRV (z (finSumFinEquiv (.inr j)))
        have he := congrFun hy j
        change (g u j).val.val = z (finSumFinEquiv (.inr j)) at he
        rw [← he]
        exact (g u j).val.property

/-- On every nonempty definable set the minimum is attained by a complete
original-base definable finite-to-one map, with no assumed dimension input. -/
theorem rvDimension_attained
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) {m : ℕ} (U : Set (Fin m → RVInfinity M))
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) (hne : U.Nonempty) :
    ∃ k : ℕ, rvDimension S U = (k : WithBot ℕ) ∧ RVHasFiniteMap S U k ∧
      ∀ l, RVHasFiniteMap S U l → k ≤ l := by
  classical
  let k := sInf {l | RVHasFiniteMap S U l}
  have hk : RVHasFiniteMap S U k := by
    change sInf {l | RVHasFiniteMap S U l} ∈ {l | RVHasFiniteMap S U l}
    exact Nat.sInf_mem ⟨m * 2, rv_finite_map_exists hc h00 S U hU⟩
  refine ⟨k, ?_, hk, fun l hl => Nat.sInf_le hl⟩
  simp only [rvDimension, ite_eq_left hne, k]

end DiamondIntegral.Section2
