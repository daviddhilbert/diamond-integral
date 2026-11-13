import «section 4».FieldBoundedCharacters
import «section 4».FieldScissorClasses
import «section 4».FieldPointCharts
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-! The dimension filtration needed for affine nonsurjectivity. Its
generators have finite coordinate fibres, with numerical bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldGrowthFiltration
open FieldDefinableRing FieldBoundedProjection
variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def Good (n : ℕ) (a : Chart K) : Prop :=
  ∃ d ≤ n, ∃ select : Fin d → Fin a.arity, ∃ C : ℕ, Bounded a.domain select C

def piece (n : ℕ) : AddSubgroup (FieldDefinableRing.Ring K) :=
  AddSubgroup.closure (Set.range (fun a : {a : Chart K // Good n a} => objectClass K a.val))

theorem chart_eq {r : ℕ} {A D : Set (Fin r → K)} (h : A = D)
    (hA : (Set.univ : Set K).Definable Language.ring A)
    (hD : (Set.univ : Set K).Definable Language.ring D) :
    (⟨r, A, hA⟩ : Chart K) = ⟨r, D, hD⟩ := by
  subst D
  rfl

theorem class_mem {n : ℕ} (a : Chart K) (ha : Good n a) : objectClass K a ∈ piece n :=
  AddSubgroup.subset_closure ⟨⟨a, ha⟩, rfl⟩

theorem good_subset {n r : ℕ} {A D : Set (Fin r → K)}
    (hA : (Set.univ : Set K).Definable Language.ring A)
    (hD : (Set.univ : Set K).Definable Language.ring D)
    (hsub : D ⊆ A) (h : Good n (⟨r, A, hA⟩ : Chart K)) :
    Good n (⟨r, D, hD⟩ : Chart K) := by
  obtain ⟨d, hd, select, C, hb⟩ := h
  exact ⟨d, hd, select, C, fun x hx he => hb x (fun i => hsub (hx i)) he⟩

theorem union_mem {n r : ℕ} {A D : Set (Fin r → K)}
    (hA : (Set.univ : Set K).Definable Language.ring A)
    (hD : (Set.univ : Set K).Definable Language.ring D)
    (ha : objectClass K ⟨r, A, hA⟩ ∈ piece n) (hd : Good n (⟨r, D, hD⟩ : Chart K)) :
    objectClass K ⟨r, A ∪ D, hA.union hD⟩ ∈ piece n := by
  have hinter := class_mem ⟨r, A ∩ D, hA.inter hD⟩
    (good_subset hD (hA.inter hD) Set.inter_subset_right hd)
  have h := FieldScissorClasses.objectClass_scissor A D (A ∪ D) (A ∩ D)
    hA hD (hA.union hD) (hA.inter hD) rfl rfl
  have he : objectClass K ⟨r, A ∪ D, hA.union hD⟩ =
      objectClass K ⟨r, A, hA⟩ + objectClass K ⟨r, D, hD⟩ -
        objectClass K ⟨r, A ∩ D, hA.inter hD⟩ := by
    exact eq_sub_of_add_eq h
  rw [he]
  exact (piece n).sub_mem ((piece n).add_mem ha (class_mem _ hd)) hinter

theorem finite_union_mem {I : Type} [Finite I] {n r : ℕ}
    (D : I → Set (Fin r → K)) (hD : ∀ i, (Set.univ : Set K).Definable Language.ring (D i))
    (hgood : ∀ i, Good n (⟨r, D i, hD i⟩ : Chart K)) :
    objectClass K ⟨r, ⋃ i, D i, Set.definable_iUnion_of_finite hD⟩ ∈ piece n := by
  letI := Fintype.ofFinite I
  have hall (s : Finset I) : ∀ hU : (Set.univ : Set K).Definable Language.ring (⋃ i ∈ s, D i),
      objectClass K ⟨r, ⋃ i ∈ s, D i, hU⟩ ∈ piece n := by
    induction s using Finset.induction_on with
    | empty =>
      intro hU
      rw [FieldPointCharts.objectClass_empty _ (by simp)]
      exact (piece n).zero_mem
    | @insert i s hi ih =>
      intro hU
      let U : Set (Fin r → K) := ⋃ j : s, D j.val
      have hU' : (Set.univ : Set K).Definable Language.ring U :=
        Set.definable_iUnion_of_finite (fun j : s => hD j.val)
      have he : U = ⋃ j ∈ s, D j := by ext x; simp [U]
      have hm : objectClass K ⟨r, U, hU'⟩ ∈ piece n := by
        subst U
        simpa only [he] using ih (he ▸ hU')
      have hmem := union_mem hU' (hD i) hm (hgood i)
      have hset : U ∪ D i = ⋃ j ∈ insert i s, D j := by
        rw [he]
        ext x
        simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
        aesop
      have heq : (⟨r, U ∪ D i, hU'.union (hD i)⟩ : Chart K) = ⟨r, ⋃ j ∈ insert i s, D j, hU⟩ := by
        exact chart_eq hset _ _
      rwa [heq] at hmem
  have hdef : (Set.univ : Set K).Definable Language.ring (⋃ i ∈ (Finset.univ : Finset I), D i) := by
    simpa using Set.definable_iUnion_of_finite hD
  simpa using hall Finset.univ hdef

end DiamondIntegral.Section4.FieldGrowthFiltration
