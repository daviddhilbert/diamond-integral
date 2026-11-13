module

public import «section 4».EulerFiniteCuts
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Range

/-! The Euler value of a finite cut cell depends only on its order pattern
and whether it is empty. This supplies fixed finite weights for uniform
families, including point, bounded interval, ray and whole-line cases. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ]

theorem cutCode_zero_iff (a x : Γ) : cutCode a x = 0 ↔ x < a := by
  rcases lt_trichotomy x a with h | h | h <;>
    simp [cutCode, h, not_lt_of_ge, le_of_lt, ne_of_gt]

theorem cutCode_one_iff (a x : Γ) : cutCode a x = 1 ↔ x = a := by
  rcases lt_trichotomy x a with h | h | h <;>
    simp [cutCode, h, not_lt_of_ge, le_of_lt, ne_of_lt, ne_of_gt]

theorem cutCode_two_iff (a x : Γ) : cutCode a x = 2 ↔ a < x := by
  rcases lt_trichotomy x a with h | h | h <;>
    simp [cutCode, h, not_lt_of_ge, le_of_lt, ne_of_gt]

def cutPatternValue {N : ℕ} (k : EulerKind) (σ : Fin N → Fin 3) : ℤ :=
  if ∃ i, σ i = 1 then 1 else
  if (∃ i, σ i = 0) ∧ (∃ i, σ i = 2) then -1 else
  if (∃ i, σ i = 0) ∨ (∃ i, σ i = 2) then k.rayValue else k.lineValue

variable [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

theorem totalEuler_cutCell (k : EulerKind) (N : ℕ) (a : Fin N → Γ) (σ : Fin N → Fin 3) :
    totalEuler k (cutCell k N a σ) =
      if ∃ x, ∀ i, cutCode (a i) x = σ i then cutPatternValue k σ else 0 := by
  by_cases hex : ∃ x, ∀ i, cutCode (a i) x = σ i
  · obtain ⟨w, hw⟩ := hex
    rw [ite_eq_left ⟨w, hw⟩]
    by_cases hp : ∃ i, σ i = 1
    · obtain ⟨j, hj⟩ := hp
      have hwj : w = a j := (cutCode_one_iff _ _).mp ((hw j).trans hj)
      have hpat (x : Γ) : (∀ i, cutCode (a i) x = σ i) ↔ x = w := by
        constructor
        · intro hx
          exact ((cutCode_one_iff _ _).mp ((hx j).trans hj)).trans hwj.symm
        · rintro rfl
          exact hw
      have he : cutCell k N a σ = point k w := by
        apply eval_injective k
        funext x
        change cutCell k N a σ x = point k w x
        simp only [cutCell_eval, point_eval, hpat]
      rw [he, totalEuler_point]
      simp only [cutPatternValue, show (∃ i, σ i = 1) from ⟨j, hj⟩, ite_true]
    · let U := (Finset.univ.filter (fun i : Fin N => σ i = 0)).image a
      let L := (Finset.univ.filter (fun i : Fin N => σ i = 2)).image a
      have hU : U.Nonempty ↔ ∃ i, σ i = 0 := by simp [U, Finset.Nonempty]
      have hL : L.Nonempty ↔ ∃ i, σ i = 2 := by simp [L, Finset.Nonempty]
      have hpat (x : Γ) : (∀ i, cutCode (a i) x = σ i) ↔
          (∀ u ∈ U, x < u) ∧ (∀ l ∈ L, l < x) := by
        constructor
        · intro hx
          constructor
          · intro u hu
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
            exact (cutCode_zero_iff _ _).mp ((hx i).trans (Finset.mem_filter.mp hi).2)
          · intro l hl
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
            exact (cutCode_two_iff _ _).mp ((hx i).trans (Finset.mem_filter.mp hi).2)
        · rintro ⟨hxU, hxL⟩ i
          have hi : σ i ≠ 1 := fun h => hp ⟨i, h⟩
          generalize he : σ i = j at hi ⊢
          fin_cases j
          · apply (cutCode_zero_iff _ _).mpr
            exact hxU (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, he⟩, rfl⟩)
          · exact (hi rfl).elim
          · apply (cutCode_two_iff _ _).mpr
            exact hxL (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, he⟩, rfl⟩)
      by_cases hu : U.Nonempty <;> by_cases hl : L.Nonempty
      · let l := L.max' hl
        let u := U.min' hu
        have hpat' (x : Γ) : (∀ i, cutCode (a i) x = σ i) ↔ l < x ∧ x < u := by
          rw [hpat]
          simp only [l, u, Finset.max'_lt_iff, Finset.lt_min'_iff, and_comm]
        have hlu : l < u := ((hpat' w).mp hw).1.trans ((hpat' w).mp hw).2
        have he : cutCell k N a σ = openInterval k l u := by
          apply eval_injective k
          funext x
          change cutCell k N a σ x = openInterval k l u x
          simp only [cutCell_eval, openInterval_eval, hpat']
        rw [he, totalEuler_openInterval, ite_eq_left hlu]
        simp only [cutPatternValue, hp, ite_false, hU.mp hu, hL.mp hl, and_self, ite_true]
      · have hLe : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hl
        let u := U.min' hu
        have hpat' (x : Γ) : (∀ i, cutCode (a i) x = σ i) ↔ x < u := by
          rw [hpat]
          simp only [hLe, Finset.notMem_empty, false_implies, implies_true, and_true,
            u, Finset.lt_min'_iff]
        have he : cutCell k N a σ = leftRay k u := by
          apply eval_injective k
          funext x
          change cutCell k N a σ x = leftRay k u x
          simp only [cutCell_eval, leftRay_eval, hpat']
        rw [he, totalEuler_leftRay]
        simp only [cutPatternValue, hp, ite_false, hU.mp hu, ← hL, hl, and_false,
          true_or, ite_true]
      · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
        let l := L.max' hl
        have hpat' (x : Γ) : (∀ i, cutCode (a i) x = σ i) ↔ l < x := by
          rw [hpat]
          simp only [hUe, Finset.notMem_empty, false_implies, implies_true, true_and,
            l, Finset.max'_lt_iff]
        have he : cutCell k N a σ = ray k l := by
          apply eval_injective k
          funext x
          change cutCell k N a σ x = ray k l x
          simp only [cutCell_eval, ray_eval, hpat']
        rw [he, totalEuler_ray]
        simp only [cutPatternValue, hp, ite_false, ← hU, hu, hL.mp hl, false_and,
          or_true, ite_true]
      · have hUe : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
        have hLe : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hl
        have he : cutCell k N a σ = line k := by
          apply eval_injective k
          funext x
          change cutCell k N a σ x = line k x
          simp only [cutCell_eval, line_eval, hpat, hUe, hLe, Finset.notMem_empty,
            false_implies, implies_true, and_self, ite_true]
        rw [he, totalEuler_line]
        simp only [cutPatternValue, hp, ite_false, ← hU, ← hL, hu, hl, false_and,
          false_or]
  · have he : cutCell k N a σ = 0 := by
      apply eval_injective k
      funext x
      change cutCell k N a σ x = (0 : EulerFunction k Γ) x
      have hx : ¬ ∀ i, cutCode (a i) x = σ i := fun h => hex ⟨x, h⟩
      simp only [cutCell_eval, hx, ite_false, eval_zero]
    rw [he, map_zero, ite_eq_right hex]

def cutEulerSum {N : ℕ} (k : EulerKind) (a : Fin N → Γ) (D : Set Γ) : ℤ :=
  ∑ σ : Fin N → Fin 3,
    if ∃ x ∈ D, ∀ i, cutCode (a i) x = σ i then cutPatternValue k σ else 0

theorem totalEuler_cut_indicator (k : EulerKind) {N : ℕ} (a : Fin N → Γ)
    (D : Set Γ) (f : EulerFunction k Γ) (hf : ∀ x, f x = if x ∈ D then 1 else 0)
    (hc : CutDetermined a f) : totalEuler k f = cutEulerSum k a D := by
  have he : ofCutFunction k a f = f := by
    apply eval_injective k
    exact funext (ofCutFunction_eval k a f hc)
  have ht (σ : Fin N → Fin 3) :
      totalEuler k (cutSampleValue a f σ • cutCell k N a σ) =
        if ∃ x ∈ D, ∀ i, cutCode (a i) x = σ i then cutPatternValue k σ else 0 := by
    by_cases hocc : ∃ x ∈ D, ∀ i, cutCode (a i) x = σ i
    · obtain ⟨x, hxD, hx⟩ := hocc
      have hex : ∃ y, ∀ i, cutCode (a i) y = σ i := ⟨x, hx⟩
      rw [map_zsmul, totalEuler_cutCell, ite_eq_left hex,
        cutSampleValue_eq a f hc σ x hx, hf, ite_eq_left hxD,
        ite_eq_left ⟨x, hxD, hx⟩, one_smul]
    · rw [ite_eq_right hocc, map_zsmul]
      by_cases hex : ∃ x, ∀ i, cutCode (a i) x = σ i
      · obtain ⟨x, hx⟩ := hex
        have hxD : x ∉ D := fun h => hocc ⟨x, h, hx⟩
        rw [cutSampleValue_eq a f hc σ x hx, hf, ite_eq_right hxD, zero_smul]
      · rw [totalEuler_cutCell, ite_eq_right hex, smul_zero]
  calc
    totalEuler k f = totalEuler k (ofCutFunction k a f) := congrArg (totalEuler k) he.symm
    _ = cutEulerSum k a D := by
      simp only [ofCutFunction, map_sum, ht, cutEulerSum]

def possibleCutEulerValues (k : EulerKind) (N : ℕ) : Set ℤ :=
  Set.range (fun b : (Fin N → Fin 3) → Bool =>
    ∑ σ : Fin N → Fin 3, if b σ then cutPatternValue k σ else 0)

theorem possibleCutEulerValues_finite (k : EulerKind) (N : ℕ) :
    (possibleCutEulerValues k N).Finite := Set.finite_range _

omit [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ] in
theorem cutEulerSum_mem_possible (k : EulerKind) {N : ℕ} (a : Fin N → Γ) (D : Set Γ) :
    cutEulerSum k a D ∈ possibleCutEulerValues k N := by
  refine ⟨(fun σ => decide (∃ x ∈ D, ∀ i, cutCode (a i) x = σ i)), ?_⟩
  simp only [cutEulerSum, decide_eq_true_eq]

end DiamondIntegral.Section4.EulerFunction
