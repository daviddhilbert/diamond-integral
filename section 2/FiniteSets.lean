import «section 2».Continuity
import «section 2».Bases
import Section3.FiniteCoding
import Section3.VFAlgebraicity

/-! Lemmas 2.12 and 2.13, with the original base and the nonzero RV target. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

omit hM in
private theorem definable_image_map {α β : Type} [Finite α] [Finite β]
    (S : Set M) (F : (α → M) → β → M) (hF : S.DefinableMap LRV F)
    (A : Set (α → M)) (hA : S.Definable LRV A) : S.Definable LRV (F '' A) := by
  have hg : S.Definable LRV {z : (β ⊕ α) → M | F (z ∘ Sum.inr) = z ∘ Sum.inl} := by
    have h (j : β) := (hF j).preimage_comp
      (fun i : Option α => i.elim (Sum.inl j) Sum.inr)
    convert Set.definable_iInter_of_finite h using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Function.tupleGraph, Set.mem_preimage]
    exact ⟨fun he j => congrFun he j, fun he => funext (fun j => he j)⟩
  have hi := ((hA.preimage_comp Sum.inr).inter hg).exists_of_finite
  convert hi using 1
  ext z
  change (∃ a, a ∈ A ∧ F a = z) ↔
    ∃ a : α → M, Sum.elim z a ∘ Sum.inr ∈ A ∧
      F (Sum.elim z a ∘ Sum.inr) = Sum.elim z a ∘ Sum.inl
  rfl

/-- Two nonzero RV entries encode one RV-infinity entry, without naming
any additional parameter. The second entry records the zero branch. -/
noncomputable def nonzeroRVCode (t : M) (j : Fin 2) : M := by
  classical
  exact if j = 0 then (if t = iRVZero then (rv M (1 : VF M)).val else t)
    else if t = iRVZero then (rv M (1 : VF M)).val else (rv M (-1 : VF M)).val

theorem nonzeroRVCode_injective
    (hne : rv M (1 : VF M) ≠ rv M (-1 : VF M)) :
    Function.Injective (nonzeroRVCode (M := M)) := by
  intro t u he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have hn : (rv M (1 : VF M)).val ≠ (rv M (-1 : VF M)).val :=
    fun h => hne (Subtype.ext h)
  by_cases ht : t = iRVZero <;> by_cases hu : u = iRVZero
  · exact ht.trans hu.symm
  · exact False.elim (hn (by simpa [nonzeroRVCode, ht, hu] using h1))
  · exact False.elim (hn (by simpa [nonzeroRVCode, ht, hu] using h1.symm))
  · simpa [nonzeroRVCode, ht, hu] using h0

theorem nonzeroRVCode_proper (t : M) (ht : iRV t) (j : Fin 2) :
    iRV (nonzeroRVCode t j) ∧ nonzeroRVCode t j ≠ iRVZero := by
  have h1 : (rv M (1 : VF M)).val ≠ iRVZero :=
    fun he => one_ne_zero ((CanonicalRV.encodedRv_zero_iff (1 : VF M)).mp he)
  have hn : (rv M (-1 : VF M)).val ≠ iRVZero :=
    fun he => (neg_ne_zero.mpr (one_ne_zero : (1 : VF M) ≠ 0))
      ((CanonicalRV.encodedRv_zero_iff (-1 : VF M)).mp he)
  by_cases hj : j = 0 <;> by_cases hz : t = iRVZero
  · simpa only [nonzeroRVCode, ite_eq_left hj, ite_eq_left hz] using
      And.intro (rv M (1 : VF M)).property h1
  · simpa only [nonzeroRVCode, ite_eq_left hj, ite_eq_right hz] using And.intro ht hz
  · simpa only [nonzeroRVCode, ite_eq_right hj, ite_eq_left hz] using
      And.intro (rv M (1 : VF M)).property h1
  · simpa only [nonzeroRVCode, ite_eq_right hj, ite_eq_right hz] using
      And.intro (rv M (-1 : VF M)).property hn

/-- Each coordinate of the parameter-free RV code is definable over the
original base; no extra names are introduced. -/
theorem nonzeroRVCode_definable {α : Type} (S : Set M) (i : α) (j : Fin 2) :
    S.DefinableFun LRV (fun z : α → M => nonzeroRVCode (z i) j) := by
  classical
  have h0 : S.Definable₁ LRV {iRVZero} :=
    SpecialTransformations.DefinableConstants.function_symbol (L := LRV) (A := S)
      Fn.rvZero Fin.elim0
      (fun i => i.elim0)
  have h1 : S.Definable₁ LRV {(1 : VF M).val} :=
    SpecialTransformations.DefinableConstants.function_symbol (L := LRV) (A := S)
      Fn.vfOne Fin.elim0
      (fun i => i.elim0)
  have hn : S.Definable₁ LRV {(-1 : VF M).val} :=
    SpecialTransformations.DefinableConstants.function_symbol Fn.vfNeg ![(1 : VF M).val]
      (by intro i; fin_cases i; exact h1)
  have hr1 : S.Definable₁ LRV {(rv M (1 : VF M)).val} :=
    SpecialTransformations.DefinableConstants.function_symbol Fn.rvMap ![(1 : VF M).val]
      (by intro i; fin_cases i; exact h1)
  have hrn : S.Definable₁ LRV {(rv M (-1 : VF M)).val} :=
    SpecialTransformations.DefinableConstants.function_symbol Fn.rvMap ![(-1 : VF M).val]
      (by intro i; fin_cases i; exact hn)
  have hc0 := SpecialTransformations.DefinableConstants.constant (α := α) h0
  have hc1 := SpecialTransformations.DefinableConstants.constant (α := α) hr1
  have hcn := SpecialTransformations.DefinableConstants.constant (α := α) hrn
  have hp : S.Definable LRV {z : α → M | z i = iRVZero} :=
    (Set.DefinableFun.proj LRV).ofPred_eq hc0
  unfold nonzeroRVCode
  split_ifs with hj
  · exact hc1.ite hp (Set.DefinableFun.proj LRV)
  · exact hc1.ite hp hcn

private noncomputable def codeTuple {m : ℕ} (t : Fin m → M) (k : Fin (m * 2)) : M :=
  nonzeroRVCode (t (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2

private noncomputable def codeGraphMap {n m : ℕ} (z : Fin (n + m) → M) : Fin (n + m * 2) → M :=
  Sum.elim (z ∘ finSumFinEquiv ∘ Sum.inl)
    (codeTuple (z ∘ finSumFinEquiv ∘ Sum.inr)) ∘ finSumFinEquiv.symm

private theorem codeGraphMap_definable (S : Set M) (n m : ℕ) :
    S.DefinableMap LRV (codeGraphMap (M := M) (n := n) (m := m)) := by
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    simpa only [codeGraphMap, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using
      (show S.DefinableFun LRV (fun z : Fin (n + m) → M => z (finSumFinEquiv (.inl j))) from
        Set.DefinableFun.proj LRV)
  | inr k =>
    simpa only [codeGraphMap, codeTuple, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inr] using
      (nonzeroRVCode_definable S
        (finSumFinEquiv (.inr (finProdFinEquiv.symm k).1) : Fin (n + m))
        (finProdFinEquiv.symm k).2)

private theorem graph_codeTuple {n m : ℕ} (A : Set (Fin n → VF M))
    (f : A → Fin m → M) :
    FiniteCoding.graph A (fun a => codeTuple (f a)) =
      codeGraphMap '' FiniteCoding.graph A f := by
  ext z
  constructor
  · rintro ⟨a, ha, hf⟩
    let w : Fin (n + m) → M :=
      Sum.elim (FiniteCoding.values a.val) (f a) ∘ finSumFinEquiv.symm
    refine ⟨w, ⟨a, ?_, ?_⟩, ?_⟩
    · funext i
      simp [w]
    · funext i
      simp [w]
    · funext i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      cases j with
      | inl j => simpa [codeGraphMap, w] using congrFun ha j
      | inr j => simpa [codeGraphMap, w, codeTuple] using congrFun hf j
  · rintro ⟨w, ⟨a, ha, hf⟩, rfl⟩
    refine ⟨a, ?_, ?_⟩
    · funext i
      simpa [codeGraphMap] using congrFun ha i
    · funext i
      simp only [codeGraphMap, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
      exact congrArg (fun t => codeTuple t i) hf

/-- Finite coding with every output coordinate in nonzero RV. -/
theorem finite_rv_coding (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {n : ℕ}
    (A : Set (Fin n → VF M)) (hfin : A.Finite)
    (hA : DefinableOver S (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ m : ℕ, ∃ f : A → Fin m → M, Function.Injective f ∧
      (∀ a j, iRV (f a j) ∧ f a j ≠ iRVZero) ∧
      DefinableOver S FiniteCoding.graphSort (FiniteCoding.graph A f) := by
  obtain ⟨m, f, hf, hs, hg⟩ := lemma_3_9 h00 S A hfin hA
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  let := hΓ
  have hne := r023_distinct_tags h00 v hv
  let g (a : A) := codeTuple (f a)
  have hinj : Function.Injective g := by
    intro a b he
    apply hf
    funext j
    apply nonzeroRVCode_injective hne
    funext k
    simpa [g, codeTuple] using congrFun he (finProdFinEquiv (j, k))
  have hproper (a : A) (j : Fin (m * 2)) : iRV (g a j) ∧ g a j ≠ iRVZero :=
    nonzeroRVCode_proper _ (hs a (finProdFinEquiv.symm j).1) _
  refine ⟨m * 2, g, hinj, hproper, ?_⟩
  apply raw_definableOver_sorted hc
  · rw [show FiniteCoding.graph A g = codeGraphMap '' FiniteCoding.graph A f from
      graph_codeTuple A f]
    exact definable_image_map S _ (codeGraphMap_definable S n m) _ hg.raw_definable
  · exact FiniteCoding.graph_sorted A g (fun a j => (hproper a j).1)

/-- Lemma 2.12 (`finite:VF:project:RV`): an actual bijection onto a definable
set in nonzero RV. The domain may have any finite VF tuple arity, and the
complete graph and image are definable over exactly the original base. -/
theorem lemma_2_12 (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {n : ℕ}
    (A : Set (Fin n → VF M)) (hfin : A.Finite)
    (hA : DefinableOver S (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ m : ℕ, ∃ U : Set (Fin m → M), ∃ e : A ≃ U,
      (∀ t ∈ U, ∀ j, iRV (t j) ∧ t j ≠ iRVZero) ∧
      DefinableOver S (fun _ => .rv) U ∧
      DefinableOver S FiniteCoding.graphSort
        (FiniteCoding.graph A (fun a => (e a).val)) := by
  obtain ⟨m, f, hf, hs, hg⟩ := finite_rv_coding hc h00 S A hfin hA
  have hrange : DefinableOver S (fun _ => .rv) (Set.range f) := by
    apply raw_definableOver_sorted hc
    · have h := hg.raw_definable.image_comp
        (fun j : Fin m => finSumFinEquiv (.inr j) : Fin m → Fin (n + m))
      convert h using 1
      ext t
      constructor
      · rintro ⟨a, rfl⟩
        let z : Fin (n + m) → M :=
          Sum.elim (FiniteCoding.values a.val) (f a) ∘ finSumFinEquiv.symm
        refine ⟨z, ⟨a, ?_, ?_⟩, ?_⟩
        all_goals funext j; simp [z]
      · rintro ⟨z, ⟨a, _, ha⟩, rfl⟩
        exact ⟨a, ha⟩
    · rintro t ⟨a, rfl⟩ j
      exact (hs a j).1
  refine ⟨m, Set.range f, Equiv.ofInjective f hf, ?_, hrange, hg⟩
  rintro t ⟨a, rfl⟩ j
  exact hs a j

/-- Lemma 2.13 (`dcl:to:ac`), coordinatewise for finite tuples. RV names do
not enlarge the VF algebraic closure over the original base and VF tuple. -/
theorem lemma_2_13 (S : Set M) {n m k : ℕ} (a : Fin n → VF M)
    (t : Fin m → RVInfinity M) (b : Fin k → VF M)
    (hb : ∀ j, AlgebraicAt ((S ∪ Set.range (fun i => (a i).val)) ∪
      Set.range (fun i => (t i).val)) .vf (b j).val) :
    ∀ j, AlgebraicAt (S ∪ Set.range (fun i => (a i).val)) .vf (b j).val := by
  intro j
  apply (algebraicAt_vf_iff_parameterField _ _).mpr
  exact lemma_3_3 S a (fun i => (t i).val) (fun i => (t i).property) (b j) (hb j)

end DiamondIntegral.Section2
