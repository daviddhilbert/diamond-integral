module

public import «section 4».EulerFiniteCuts
public import Mathlib.Data.Set.Card

/-! Euler integration of actual finite sets is their cardinality, for both
Euler theories. No definable-choice or parameter-naming assumption is used. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

theorem exists_fin_inj_of_finite_ncard {α : Type*} (A : Set α) (hA : A.Finite)
    {n : ℕ} (hcard : A.ncard = n) :
    ∃ u : Fin n → α, Function.Injective u ∧ ∀ i, u i ∈ A := by
  have hc : hA.toFinset.card = n := (Set.ncard_eq_toFinset_card A hA).symm.trans hcard
  let e := (Finset.equivFinOfCardEq hc).symm
  exact ⟨(fun i => (e i).val),
    (fun _ _ h => e.injective (Subtype.ext h)),
    (fun i => hA.mem_toFinset.mp (e i).property)⟩

theorem finite_ncard_le_iff_no_inj {α : Type*} (A : Set α) (N : ℕ) :
    A.Finite ∧ A.ncard ≤ N ↔
      ¬ ∃ u : Fin (N + 1) → α, Function.Injective u ∧ ∀ i, u i ∈ A := by
  constructor
  · rintro ⟨hA, hcard⟩ ⟨u, hu, hmem⟩
    have h : (Set.univ : Set (Fin (N + 1))).ncard ≤ A.ncard :=
      Set.ncard_le_ncard_of_injOn u (fun i _ => hmem i)
      (fun _ _ _ _ h => hu h) hA
    rw [Set.ncard_univ] at h
    simp only [Nat.card_fin] at h
    omega
  · intro h
    have hA : A.Finite := by
      by_contra hi
      obtain ⟨C, hCA, hC, hcard⟩ := Set.Infinite.exists_subset_ncard_eq hi (N + 1)
      obtain ⟨u, hu, hmem⟩ := exists_fin_inj_of_finite_ncard C hC hcard
      exact h ⟨u, hu, fun i => hCA (hmem i)⟩
    refine ⟨hA, ?_⟩
    by_contra hcard
    obtain ⟨C, hCA, hcardC⟩ := Set.exists_subset_card_eq (show N + 1 ≤ A.ncard by omega)
    obtain ⟨u, hu, hmem⟩ := exists_fin_inj_of_finite_ncard C (hA.subset hCA) hcardC
    exact h ⟨u, hu, fun i => hCA (hmem i)⟩

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def finiteIndicator (k : EulerKind) (A : Finset Γ) : EulerFunction k Γ :=
  ∑ a ∈ A, point k a

theorem finiteIndicator_eval (k : EulerKind) (A : Finset Γ) (x : Γ) :
    finiteIndicator k A x = if x ∈ A then 1 else 0 := by
  simp only [finiteIndicator, eval_finsetSum, point_eval]
  simp_rw [eq_comm (a := x)]
  rw [Finset.sum_ite_eq']

theorem totalEuler_finiteIndicator (k : EulerKind) (A : Finset Γ) :
    totalEuler k (finiteIndicator k A) = A.card := by
  simp only [finiteIndicator, map_sum, totalEuler_point, Finset.sum_const, nsmul_eq_mul,
    mul_one]

theorem totalEuler_finite_set (k : EulerKind) (A : Set Γ) (hA : A.Finite)
    (f : EulerFunction k Γ) (hf : ∀ x, f x = if x ∈ A then 1 else 0) :
    totalEuler k f = A.ncard := by
  have he : f = finiteIndicator k hA.toFinset := by
    apply eval_injective k
    funext x
    change f x = finiteIndicator k hA.toFinset x
    rw [hf, finiteIndicator_eval]
    by_cases hx : x ∈ A
    · simp [hx, hA.mem_toFinset.mpr hx]
    · have hn : x ∉ hA.toFinset := fun h => hx (hA.mem_toFinset.mp h)
      simp [hx, hn]
  rw [he, totalEuler_finiteIndicator, Set.ncard_eq_toFinset_card A hA]

theorem totalEuler_finite_set_equiv {α : Type*} (k : EulerKind) (A : Set α)
    (hA : A.Finite) (e : α ≃ Γ) (f : EulerFunction k Γ)
    (hf : ∀ x, f (e x) = if x ∈ A then 1 else 0) : totalEuler k f = A.ncard := by
  have he : totalEuler k f = (e '' A).ncard := by
    apply totalEuler_finite_set k (e '' A) (hA.image e) f
    intro x
    obtain ⟨a, rfl⟩ := e.surjective x
    rw [hf]
    by_cases ha : a ∈ A
    · simp only [ha, ite_true, Set.mem_image_of_mem e ha]
    · have hn : e a ∉ e '' A := by
        rintro ⟨b, hb, hba⟩
        exact ha ((e.injective hba) ▸ hb)
      simp only [ha, hn, ite_false]
  exact he.trans (congrArg (fun n : ℕ => (n : ℤ)) (Set.ncard_image_of_injective A e.injective))

end DiamondIntegral.Section4.EulerFunction
