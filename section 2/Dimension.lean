import «section 2».Conventions
import Section4.PolydiscLocal

/-!
# VF dimension, Definition 2.16 and Lemma 2.17

The definition follows the manuscript's coordinate projections and nonempty
interior. The author-approved empty-set value is bottom, written −∞.
-/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Set Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

section Topological

omit hM

variable [TopologicalSpace (VF M)]

/-- The manuscript's witness of k-dimensional VF interior, after choosing
k distinct VF coordinates and fixing all original RV labels. -/
def HasVFInteriorDim {n m : ℕ} (A : Set (Mixed M n m)) (k : ℕ) : Prop :=
  ∃ e : Fin k ↪ Fin n, ∃ t : Fin m → RVInfinity M,
    (interior ((fun a : Fin n → VF M => a ∘ e) '' vfFibre A t)).Nonempty

/-- The maximum witnessed interior dimension. A finite maximum in WithBot
gives −∞ precisely when no dimension is witnessed, including the empty set. -/
noncomputable def vfDimension {n m : ℕ} (A : Set (Mixed M n m)) : WithBot ℕ := by
  classical
  exact (Finset.univ : Finset (Fin (n + 1))).sup
    (fun k => if HasVFInteriorDim A k.val then (k.val : WithBot ℕ) else ⊥)

theorem HasVFInteriorDim.le_arity {n m k : ℕ} {A : Set (Mixed M n m)}
    (h : HasVFInteriorDim A k) : k ≤ n := by
  obtain ⟨e, _, _⟩ := h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective

theorem HasVFInteriorDim.le_dimension {n m k : ℕ} {A : Set (Mixed M n m)}
    (h : HasVFInteriorDim A k) : (k : WithBot ℕ) ≤ vfDimension A := by
  classical
  let i : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le h.le_arity⟩
  apply Finset.le_sup_of_le (s := Finset.univ)
    (f := fun j : Fin (n + 1) => if HasVFInteriorDim A j.val then (j.val : WithBot ℕ) else ⊥)
    (Finset.mem_univ i)
  change (k : WithBot ℕ) ≤ if HasVFInteriorDim A k then (k : WithBot ℕ) else ⊥
  rw [ite_eq_left h]

theorem vfDimension_eq_iff {n m k : ℕ} (A : Set (Mixed M n m)) :
    vfDimension A = (k : WithBot ℕ) ↔
      HasVFInteriorDim A k ∧ ∀ l, HasVFInteriorDim A l → l ≤ k := by
  classical
  constructor
  · intro he
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (n + 1)))
      ⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩
      (fun i => if HasVFInteriorDim A i.val then (i.val : WithBot ℕ) else ⊥)
    change vfDimension A = _ at hi
    by_cases hp : HasVFInteriorDim A i.val
    · rw [ite_eq_left hp, he] at hi
      have hik : i.val = k := (WithBot.coe_eq_coe.mp hi).symm
      refine ⟨hik ▸ hp, ?_⟩
      intro l hl
      have hle := hl.le_dimension
      rw [he] at hle
      exact WithBot.coe_le_coe.mp hle
    · rw [ite_eq_right hp, he] at hi
      exact (WithBot.coe_ne_bot hi).elim
  · rintro ⟨hk, hmax⟩
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      by_cases hp : HasVFInteriorDim A i.val
      · rw [ite_eq_left hp]
        exact WithBot.coe_le_coe.mpr (hmax i.val hp)
      · simp only [ite_eq_right hp, bot_le]
    · exact hk.le_dimension

@[simp] theorem vfDimension_empty (n m : ℕ) :
    vfDimension (∅ : Set (Mixed M n m)) = ⊥ := by
  classical
  simp [vfDimension, HasVFInteriorDim, vfFibre]

theorem hasVFInteriorDim_zero_iff {n m : ℕ} (A : Set (Mixed M n m)) :
    HasVFInteriorDim A 0 ↔ A.Nonempty := by
  constructor
  · rintro ⟨e, t, x, hx⟩
    obtain ⟨a, ha, _⟩ := interior_subset hx
    exact ⟨(a, t), ha⟩
  · rintro ⟨⟨a, t⟩, ha⟩
    let e : Fin 0 ↪ Fin n := ⟨Fin.elim0, fun i => i.elim0⟩
    refine ⟨e, t, ?_⟩
    have he : (fun a : Fin n → VF M => a ∘ e) '' vfFibre A t = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact ⟨a, ha, funext (fun i => i.elim0)⟩
    rw [he, interior_univ]
    exact Set.univ_nonempty

@[simp] theorem vfDimension_eq_bot_iff {n m : ℕ} (A : Set (Mixed M n m)) :
    vfDimension A = ⊥ ↔ A = ∅ := by
  constructor
  · intro hd
    by_contra hn
    have h := ((hasVFInteriorDim_zero_iff A).mpr (Set.nonempty_iff_ne_empty.mpr hn)).le_dimension
    rw [hd] at h
    simp at h
  · rintro rfl
    exact vfDimension_empty n m

theorem vfDimension_eq_full_iff {n m : ℕ} (A : Set (Mixed M n m)) :
    vfDimension A = (n : WithBot ℕ) ↔
      ∃ t : Fin m → RVInfinity M, (interior (vfFibre A t)).Nonempty := by
  rw [vfDimension_eq_iff]
  constructor
  · rintro ⟨⟨e, t, ht⟩, _⟩
    let E : Fin n ≃ Fin n := Equiv.ofBijective e
      ((Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, rfl⟩)
    let H : (Fin n → VF M) ≃ₜ (Fin n → VF M) :=
      { toFun := fun a => a ∘ E
        invFun := fun a => a ∘ E.symm
        left_inv := fun a => by funext i; exact congrArg a (E.apply_symm_apply i)
        right_inv := fun a => by funext i; exact congrArg a (E.symm_apply_apply i)
        continuous_toFun := continuous_pi (fun i => continuous_apply (E i))
        continuous_invFun := continuous_pi (fun i => continuous_apply (E.symm i)) }
    change (interior (H '' vfFibre A t)).Nonempty at ht
    rw [← H.image_interior] at ht
    exact ⟨t, Set.image_nonempty.mp ht⟩
  · rintro ⟨t, ht⟩
    have hp : HasVFInteriorDim A n := by
      refine ⟨Function.Embedding.refl _, t, ?_⟩
      change (interior ((fun a : Fin n → VF M => a) '' vfFibre A t)).Nonempty
      have hi : (fun a : Fin n → VF M => a) '' vfFibre A t = vfFibre A t := by
        ext a
        simp
      rw [hi]
      exact ht
    exact ⟨hp, fun _ h => h.le_arity⟩

end Topological

section Valuation

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VF M) Γ]

/-- Lemma 2.17 (`full:dim:open:poly`), including empty sets and zero VF
coordinates under the approved −∞ convention. The equivalence is geometric,
so no definability or saturation hypothesis is needed. -/
theorem lemma_2_17 {n m : ℕ} (A : Set (Mixed M n m)) :
    vfDimension A = (n : WithBot ℕ) ↔
      ∃ t : Fin m → RVInfinity M,
        ∃ D : SpecialTransformations.Section4.ValuedPolydisc
          (Valued.v : Valuation (VF M) Γ) n, D.carrier ⊆ vfFibre A t := by
  rw [vfDimension_eq_full_iff]
  constructor
  · rintro ⟨t, a, ha⟩
    obtain ⟨D, _, hD⟩ := SpecialTransformations.Section4.exists_polydisc_subset_of_mem_nhds
      a (mem_interior_iff_mem_nhds.mp ha)
    exact ⟨t, D, hD⟩
  · rintro ⟨t, D, hD⟩
    have he : D.carrier = Set.pi Set.univ D.side :=
      Set.ext (fun a => D.mem_carrier_iff a)
    have hn : D.carrier ∈ 𝓝 D.centre := by
      rw [he]
      exact set_pi_mem_nhds Set.finite_univ (fun i _ => D.side_mem_nhds i)
    exact ⟨t, D.centre, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hn hD)⟩

end Valuation

end DiamondIntegral.Section2
