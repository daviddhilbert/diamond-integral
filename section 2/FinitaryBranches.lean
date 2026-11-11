import «section 2».FinitaryCoding
import Section8.ContinuityFamilies

/-!
# Definable inverse branches of uniform finite RV codes

Each code has at most one value in a fibre. Its inverse branch is extended
by zero when absent. This is unique definable inversion, without a definable
choice hypothesis, uniformly over the original parameter base.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2.FinitaryRVCode
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {S : Set M} {A : Set (Fin n → VF M)}
variable {F : (Fin n → VF M) → Set (Fin m → VF M)}

def codedGraph (C : FinitaryRVCode S A F) :
    Set (Fin C.arity ⊕ (Fin n ⊕ Fin m) → M) :=
  {z | z ∘ Sum.inr ∈ vfCorrespondenceGraph A F ∧
    C.code ((z ∘ Sum.inr) ∘ Sum.inl) ((z ∘ Sum.inr) ∘ Sum.inr) = z ∘ Sum.inl}

omit hM in
theorem codedGraph_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV C.codedGraph := by
  have hcode (j : Fin C.arity) : S.Definable LRV
      {z : Fin C.arity ⊕ (Fin n ⊕ Fin m) → M |
        C.code ((z ∘ Sum.inr) ∘ Sum.inl) ((z ∘ Sum.inr) ∘ Sum.inr) j = z (.inl j)} :=
    ((C.definable j).comp (fun _ => Set.DefinableFun.proj LRV)).ofPred_eq
      (Set.DefinableFun.proj LRV)
  convert (hG.preimage_comp Sum.inr).inter (Set.definable_iInter_of_finite hcode) using 1
  ext z
  simp only [codedGraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  exact and_congr_right (fun _ => funext_iff)

def branchDomain (C : FinitaryRVCode S A F) : Set (Fin C.arity ⊕ Fin n → M) :=
  {z | ∃ y : Fin m → M, Sum.elim (z ∘ Sum.inl) (Sum.elim (z ∘ Sum.inr) y) ∈ C.codedGraph}

omit hM in
theorem branchDomain_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV C.branchDomain := by
  let e : Fin C.arity ⊕ (Fin n ⊕ Fin m) → (Fin C.arity ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  convert ((C.codedGraph_definable hG).preimage_comp e).exists_of_finite using 1
  ext z
  apply exists_congr
  intro y
  have he : Sum.elim z y ∘ e = Sum.elim (z ∘ Sum.inl) (Sum.elim (z ∘ Sum.inr) y) := by
    funext i
    rcases i with i | i | i <;> rfl
  rw [Set.mem_preimage, he]

def branchGraph (C : FinitaryRVCode S A F) :
    Set (Fin C.arity ⊕ (Fin n ⊕ Fin m) → M) :=
  C.codedGraph ∪ {z | (z ∘ Sum.inr) ∘ Sum.inl ∈ vfRawUniverse n ∧
    (z ∘ Sum.inr) ∘ Sum.inr = vfValues (0 : Fin m → VF M) ∧
    Sum.elim (z ∘ Sum.inl) ((z ∘ Sum.inr) ∘ Sum.inl) ∉ C.branchDomain}

theorem branchGraph_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV C.branchGraph := by
  let Z := Fin C.arity ⊕ (Fin n ⊕ Fin m)
  have hz : S.DefinableFun LRV (fun _ : Z → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hzero : S.Definable LRV {z : Z → M |
      (z ∘ Sum.inr) ∘ Sum.inr = vfValues (0 : Fin m → VF M)} := by
    convert Set.definable_iInter_of_finite (fun j : Fin m =>
      (Set.DefinableFun.proj LRV (i := (Sum.inr (Sum.inr j) : Z))).ofPred_eq hz) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact funext_iff
  let e : Fin C.arity ⊕ Fin n → Z := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  exact (C.codedGraph_definable hG).union
    (((vfRawUniverse_definable S n).preimage_comp (Sum.inr ∘ Sum.inl)).inter
      (hzero.inter ((C.branchDomain_definable hG).preimage_comp e).compl))

def HasValue (C : FinitaryRVCode S A F) (t : Fin C.arity → M)
    (a : Fin n → VF M) (y : Fin m → VF M) : Prop :=
  a ∈ A ∧ y ∈ F a ∧ C.code (vfValues a) (vfValues y) = t

noncomputable def branch (C : FinitaryRVCode S A F) (t : Fin C.arity → M)
    (a : Fin n → VF M) : Fin m → VF M := by
  classical
  exact if h : ∃ y, C.HasValue t a y then h.choose else 0

omit hM in
theorem hasValue_unique (C : FinitaryRVCode S A F) {t a y z}
    (hy : C.HasValue t a y) (hz : C.HasValue t a z) : y = z :=
  C.injective a hy.1 hy.2.1 hz.2.1 (hy.2.2.trans hz.2.2.symm)

theorem branch_eq_of_hasValue (C : FinitaryRVCode S A F) {t a y}
    (hy : C.HasValue t a y) : C.branch t a = y := by
  classical
  have h : ∃ y, C.HasValue t a y := ⟨y, hy⟩
  rw [branch, dite_eq_left h]
  exact C.hasValue_unique h.choose_spec hy

theorem hasValue_branch (C : FinitaryRVCode S A F) {t a}
    (h : ∃ y, C.HasValue t a y) : C.HasValue t a (C.branch t a) := by
  classical
  rw [branch, dite_eq_left h]
  exact h.choose_spec

omit hM in
theorem mem_codedGraph (C : FinitaryRVCode S A F) (t : Fin C.arity → M)
    (a : Fin n → VF M) (y : Fin m → VF M) :
    Sum.elim t (Sum.elim (vfValues a) (vfValues y)) ∈ C.codedGraph ↔ C.HasValue t a y := by
  constructor
  · rintro ⟨⟨b, hb, c, hc, he⟩, ht⟩
    have hba : b = a := vfValues_injective (funext (fun i => congrFun he (.inl i)))
    have hcy : c = y := vfValues_injective (funext (fun i => congrFun he (.inr i)))
    subst b; subst c
    exact ⟨hb, hc, ht⟩
  · rintro ⟨ha, hy, ht⟩
    exact ⟨⟨a, ha, y, hy, rfl⟩, ht⟩

omit hM in
theorem mem_branchDomain (C : FinitaryRVCode S A F) (t : Fin C.arity → M)
    (a : Fin n → VF M) :
    Sum.elim t (vfValues a) ∈ C.branchDomain ↔ ∃ y, C.HasValue t a y := by
  constructor
  · rintro ⟨y, ⟨⟨b, hb, c, hc, he⟩, ht⟩⟩
    have hba : b = a := vfValues_injective (funext (fun i => congrFun he (.inl i)))
    subst b
    have hy : vfValues c = y := funext (fun i => congrFun he (.inr i))
    exact ⟨c, hb, hc, hy.symm ▸ ht⟩
  · rintro ⟨y, hy⟩
    exact ⟨vfValues y, (C.mem_codedGraph t a y).mpr hy⟩

theorem branchGraph_slice (C : FinitaryRVCode S A F) (t : Fin C.arity → M) :
    {z | Sum.elim t z ∈ C.branchGraph} = vfGraph (C.branch t) := by
  classical
  ext z
  constructor
  · rintro (hz | ⟨ha, hy, hn⟩)
    · obtain ⟨⟨a, ha, y, hy, he⟩, ht⟩ := hz
      change Sum.elim (vfValues a) (vfValues y) = z at he
      change C.code (z ∘ Sum.inl) (z ∘ Sum.inr) = t at ht
      rw [← he] at ht
      have hb : C.branch t a = y := C.branch_eq_of_hasValue ⟨ha, hy, ht⟩
      exact ⟨a, by simpa only [hb] using he⟩
    · let a : Fin n → VF M := fun i => ⟨z (.inl i), ha i⟩
      have hnone : ¬ ∃ y, C.HasValue t a y :=
        fun h => hn ((C.mem_branchDomain t a).mpr h)
      have hb : C.branch t a = 0 := by rw [branch, dite_eq_right hnone]
      refine ⟨a, ?_⟩
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (congrArg Subtype.val (congrFun hb i)).trans (congrFun hy i).symm
  · rintro ⟨a, rfl⟩
    by_cases h : ∃ y, C.HasValue t a y
    · exact Or.inl ((C.mem_codedGraph t a _).mpr (C.hasValue_branch h))
    · refine Or.inr ⟨fun i => (a i).property, ?_, ?_⟩
      · have hb : C.branch t a = 0 := by rw [branch, dite_eq_right h]
        exact congrArg vfValues hb
      · exact fun hn => h ((C.mem_branchDomain t a).mp hn)

end DiamondIntegral.Section2.FinitaryRVCode
