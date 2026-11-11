import «section 2».Conventions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Section3.DefinableConstants

/-! Finite coordinate charts for the zero-pattern split in 2.35.
Fixed coordinates are listed first; free coordinates retain their order
through an explicit finite equivalence. No model element is chosen. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

structure ZeroFaceChart {n : ℕ} (Z : Set (Fin n)) where
  zeroArity : ℕ
  freeArity : ℕ
  coordinates : Fin (zeroArity+freeArity) ≃ Fin n
  zero_mem : ∀ i, coordinates (Fin.castAdd freeArity i) ∈ Z
  free_not_mem : ∀ i, coordinates (Fin.natAdd zeroArity i) ∉ Z

noncomputable def zeroFaceChart {n : ℕ} (Z : Set (Fin n)) : ZeroFaceChart Z := by
  classical
  let p := Fintype.card Z
  let r := Fintype.card (Zᶜ : Set (Fin n))
  let ep : Fin p ≃ Z := (Fintype.equivFin Z).symm
  let er : Fin r ≃ (Zᶜ : Set (Fin n)) := (Fintype.equivFin (Zᶜ : Set (Fin n))).symm
  let e : Fin (p+r) ≃ Fin n :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr ep er).trans (Equiv.Set.sumCompl Z))
  refine ⟨p,r,e,?_,?_⟩
  · intro i
    simpa only [e,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.Set.sumCompl_apply_inl,
      finSumFinEquiv_symm_apply_castAdd,Sum.map_inl] using (ep i).property
  · intro i
    simpa only [e,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.Set.sumCompl_apply_inr,
      finSumFinEquiv_symm_apply_natAdd,Sum.map_inr,Set.mem_compl_iff] using (er i).property

def ZeroFaceChart.zeroIndex {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) (i : Fin C.zeroArity) : Fin n :=
  C.coordinates (Fin.castAdd C.freeArity i)

def ZeroFaceChart.freeIndex {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) (i : Fin C.freeArity) : Fin n :=
  C.coordinates (Fin.natAdd C.zeroArity i)

theorem ZeroFaceChart.coordinate_cases {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) (j : Fin n) :
    (∃ i, j = C.zeroIndex i) ∨ ∃ i, j = C.freeIndex i := by
  obtain ⟨k,rfl⟩ := C.coordinates.surjective j
  exact Fin.addCases (fun i => Or.inl ⟨i,rfl⟩) (fun i => Or.inr ⟨i,rfl⟩) k

def ZeroFaceChart.insert {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (x : Fin C.freeArity → α) : Fin n → α :=
  Fin.append (fun _ : Fin C.zeroArity => z) x ∘ C.coordinates.symm

def ZeroFaceChart.project {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (y : Fin n → α) : Fin C.freeArity → α := y ∘ C.freeIndex

theorem ZeroFaceChart.insert_zero {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (x : Fin C.freeArity → α) (i : Fin C.zeroArity) : C.insert z x (C.zeroIndex i) = z := by
  simp only [ZeroFaceChart.insert,ZeroFaceChart.zeroIndex,Function.comp_apply,
    C.coordinates.symm_apply_apply,Fin.append_left]

theorem ZeroFaceChart.insert_free {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (x : Fin C.freeArity → α) (i : Fin C.freeArity) : C.insert z x (C.freeIndex i) = x i := by
  simp only [ZeroFaceChart.insert,ZeroFaceChart.freeIndex,Function.comp_apply,
    C.coordinates.symm_apply_apply,Fin.append_right]

theorem ZeroFaceChart.project_insert {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (x : Fin C.freeArity → α) : C.project (C.insert z x) = x :=
  funext (C.insert_free z x)

theorem ZeroFaceChart.insert_project {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (y : Fin n → α) (hy : ∀ i, y (C.zeroIndex i) = z) : C.insert z (C.project y) = y := by
  funext j
  rcases C.coordinate_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [C.insert_zero]
    exact (hy i).symm
  · rw [C.insert_free]
    rfl

theorem ZeroFaceChart.insert_injective {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) : Function.Injective (C.insert z) := by
  intro x y h
  have hp := congrArg C.project h
  simpa only [C.project_insert] using hp

def ZeroFaceChart.slice {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (D : Set (Fin n → α)) : Set (Fin C.freeArity → α) :=
  {x | C.insert z x ∈ D ∧ ∀ i, x i ≠ z}

def ZeroFaceChart.lift {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (V : Set (Fin C.freeArity → α)) : Set (Fin n → α) :=
  {y | (∀ i, y (C.zeroIndex i) = z) ∧ C.project y ∈ V}

theorem ZeroFaceChart.lift_subset {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (D : Set (Fin n → α)) (V : Set (Fin C.freeArity → α)) (hV : V ⊆ C.slice z D) :
    C.lift z V ⊆ D := by
  intro y hy
  have h := (hV hy.2).1
  rwa [C.insert_project z y hy.1] at h

theorem ZeroFaceChart.lift_disjoint {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (V W : Set (Fin C.freeArity → α)) (hVW : Disjoint V W) :
    Disjoint (C.lift z V) (C.lift z W) :=
  Set.disjoint_left.mpr (fun _ hy hz => Set.disjoint_left.mp hVW hy.2 hz.2)

theorem ZeroFaceChart.lift_zero_pattern {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (V : Set (Fin C.freeArity → α)) (hV : ∀ x ∈ V, ∀ i, x i ≠ z)
    (y : Fin n → α) (hy : y ∈ C.lift z V) (j : Fin n) : y j = z ↔ j ∈ Z := by
  rcases C.coordinate_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨fun _ => C.zero_mem i,fun _ => hy.1 i⟩
  · exact ⟨fun h => (hV _ hy.2 i h).elim,fun h => (C.free_not_mem i h).elim⟩

theorem ZeroFaceChart.lift_other_disjoint {n : ℕ} {Z W : Set (Fin n)}
    (C : ZeroFaceChart Z) (E : ZeroFaceChart W) {α : Type*} (z : α)
    (V : Set (Fin C.freeArity → α)) (T : Set (Fin E.freeArity → α))
    (hV : ∀ x ∈ V, ∀ i, x i ≠ z) (hT : ∀ x ∈ T, ∀ i, x i ≠ z) (hne : Z ≠ W) :
    Disjoint (C.lift z V) (E.lift z T) := by
  apply Set.disjoint_left.mpr
  intro y hy ht
  apply hne
  ext j
  exact (C.lift_zero_pattern z V hV y hy j).symm.trans (E.lift_zero_pattern z T hT y ht j)

theorem ZeroFaceChart.slice_project {n : ℕ} {Z : Set (Fin n)} (C : ZeroFaceChart Z) {α : Type*}
    (z : α) (D : Set (Fin n → α)) (y : Fin n → α) (hy : y ∈ D)
    (hpattern : ∀ j, y j = z ↔ j ∈ Z) : C.project y ∈ C.slice z D := by
  have hzero : ∀ i, y (C.zeroIndex i) = z := fun i => (hpattern _).mpr (C.zero_mem i)
  refine ⟨?_,?_⟩
  · rwa [C.insert_project z y hzero]
  · intro i he
    exact C.free_not_mem i ((hpattern _).mp he)

variable {M : Type} [LRV.Structure M]

theorem ZeroFaceChart.insert_definable (S : Set M) {n : ℕ} {Z : Set (Fin n)}
    (C : ZeroFaceChart Z) (z : M) (hz : S.Definable₁ LRV {z}) : S.DefinableMap LRV (C.insert z) := by
  intro j
  rcases C.coordinate_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · have he : (fun x => C.insert z x (C.zeroIndex i)) = (fun _ : Fin C.freeArity → M => z) :=
      funext (fun x => C.insert_zero z x i)
    rw [he]
    exact SpecialTransformations.DefinableConstants.constant hz
  · have he : (fun x => C.insert z x (C.freeIndex i)) = (fun x : Fin C.freeArity → M => x i) :=
      funext (fun x => C.insert_free z x i)
    rw [he]
    exact Set.DefinableFun.proj LRV

theorem ZeroFaceChart.slice_definable (S : Set M) {n : ℕ} {Z : Set (Fin n)}
    (C : ZeroFaceChart Z) (z : M) (hz : S.Definable₁ LRV {z}) (D : Set (Fin n → M))
    (hD : S.Definable LRV D) : S.Definable LRV (C.slice z D) := by
  have hne := Set.definable_iInter_of_finite (fun i : Fin C.freeArity =>
    ((Set.DefinableFun.proj LRV (i := i)).ofPred_eq
      (SpecialTransformations.DefinableConstants.constant hz)).compl)
  convert (hD.preimage_map (C.insert_definable S z hz)).inter hne using 1
  ext x
  simp only [ZeroFaceChart.slice,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,
    Set.mem_iInter,Set.mem_compl_iff]

theorem ZeroFaceChart.lift_definable (S : Set M) {n : ℕ} {Z : Set (Fin n)}
    (C : ZeroFaceChart Z) (z : M) (hz : S.Definable₁ LRV {z}) (V : Set (Fin C.freeArity → M))
    (hV : S.Definable LRV V) : S.Definable LRV (C.lift z V) := by
  have hzero := Set.definable_iInter_of_finite (fun i : Fin C.zeroArity =>
    (Set.DefinableFun.proj LRV (i := C.zeroIndex i)).ofPred_eq
      (SpecialTransformations.DefinableConstants.constant hz))
  convert hzero.inter (hV.preimage_comp C.freeIndex) using 1
  ext y
  simp only [ZeroFaceChart.lift,ZeroFaceChart.project,Set.mem_ofPred_eq,Set.mem_inter_iff,
    Set.mem_iInter,Set.mem_preimage]

end DiamondIntegral.Section2
