module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Set.Card

/-! Canonical ordered ranks in finite sets. The kth point is characterized
by membership and exactly k smaller points; this will define boundary
functions without choosing RV representatives. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.FiniteOrderRanks

variable {α : Type*} [LinearOrder α]

def rank (A : Finset α) (x : α) : ℕ := (A.filter (fun a => a < x)).card

theorem rank_lt_card (A : Finset α) (x : α) (hx : x ∈ A) : rank A x < A.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨x, hx, lt_irrefl x⟩)

theorem rank_orderIsoOfFin (A : Finset α) (i : Fin A.card) :
    rank A (A.orderIsoOfFin rfl i).val = i.val := by
  let e := A.orderIsoOfFin rfl
  have he : (Finset.Iio i).card = (A.filter (fun a => a < (e i).val)).card := by
    apply Finset.card_bij (fun j _ => (e j).val)
    · intro j hj
      exact Finset.mem_filter.mpr ⟨(e j).property, e.strictMono (Finset.mem_Iio.mp hj)⟩
    · intro j hj l hl h
      exact e.injective (Subtype.ext h)
    · intro x hx
      obtain ⟨hxA, hxi⟩ := Finset.mem_filter.mp hx
      let j := e.symm ⟨x, hxA⟩
      have hj : j < i := by
        apply e.lt_iff_lt.mp
        change (e j).val < (e i).val
        simpa only [j, e.apply_symm_apply] using hxi
      exact ⟨j, Finset.mem_Iio.mpr hj, congrArg Subtype.val (e.apply_symm_apply ⟨x, hxA⟩)⟩
  change (A.filter (fun a => a < (e i).val)).card = i.val
  rw [← he, Fin.card_Iio]

theorem rank_strictMonoOn (A : Finset α) : StrictMonoOn (rank A) (A : Set α) := by
  intro x hx y hy hxy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨haA, hax⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨haA, hax.trans hxy⟩
  · intro he
    have hxin : x ∈ A.filter (fun a => a < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    have hxout : x ∉ A.filter (fun a => a < x) := by simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]
    exact hxout (he.symm ▸ hxin)

theorem exists_unique_rank (A : Finset α) (k : ℕ) (hk : k < A.card) :
    ∃! x, x ∈ A ∧ rank A x = k := by
  let i : Fin A.card := ⟨k, hk⟩
  let e := A.orderIsoOfFin rfl
  refine ⟨(e i).val, ⟨(e i).property, rank_orderIsoOfFin A i⟩, ?_⟩
  rintro x ⟨hx, hr⟩
  apply (rank_strictMonoOn A).injOn hx (e i).property
  exact hr.trans (rank_orderIsoOfFin A i).symm

def setRank (A : Set α) (x : α) : ℕ := {a | a ∈ A ∧ a < x}.ncard

theorem setRank_toFinset (A : Set α) (hA : A.Finite) (x : α) :
    setRank A x = rank hA.toFinset x := by
  have he : {a | a ∈ A ∧ a < x} = (hA.toFinset.filter (fun a => a < x) : Set α) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, hA.mem_toFinset]
  rw [setRank, he, Set.ncard_coe_finset]
  rfl

theorem setRank_lt_ncard (A : Set α) (hA : A.Finite) (x : α) (hx : x ∈ A) :
    setRank A x < A.ncard := by
  rw [setRank_toFinset A hA x, Set.ncard_eq_toFinset_card A hA]
  exact rank_lt_card hA.toFinset x (hA.mem_toFinset.mpr hx)

theorem exists_unique_setRank (A : Set α) (hA : A.Finite) (k : ℕ) (hk : k < A.ncard) :
    ∃! x, x ∈ A ∧ setRank A x = k := by
  have hk' : k < hA.toFinset.card := by simpa only [Set.ncard_eq_toFinset_card A hA] using hk
  obtain ⟨x, hx, huniq⟩ := exists_unique_rank hA.toFinset k hk'
  refine ⟨x, ⟨hA.mem_toFinset.mp hx.1, ?_⟩, ?_⟩
  · rw [setRank_toFinset]
    exact hx.2
  · rintro y ⟨hy, hr⟩
    apply huniq y
    exact ⟨hA.mem_toFinset.mpr hy, (setRank_toFinset A hA y).symm.trans hr⟩

end DiamondIntegral.Section4.FiniteOrderRanks
