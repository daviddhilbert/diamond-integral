import «section 2».DiscParameters

/-! Equality of actual disc names under a change of centre inside the
disc. Open discs retain finite radii throughout. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

omit hM in
theorem disc_underlying_subset_vf (D : DC (M := M)) :
    BallImaginaries.underlying D ⊆ {x | iVF x} := by
  induction D using Quotient.inductionOn with
  | h c =>
    cases c with
    | inl C =>
      induction C using Quotient.inductionOn with
      | h q => exact fun _ hx => hx.2.1
    | inr O =>
      induction O using Quotient.inductionOn with
      | h q => exact fun _ hx => hx.2.1

omit hM in
theorem discPoints_injective : Function.Injective (discPoints (M := M)) := by
  intro D E h
  apply BallImaginaries.underlying_injective
  ext x
  constructor
  · intro hx
    let a : VF M := ⟨x, disc_underlying_subset_vf D hx⟩
    have ha : a ∈ discPoints D := hx
    exact (Set.ext_iff.mp h a).mp ha
  · intro hx
    let a : VF M := ⟨x, disc_underlying_subset_vf E hx⟩
    have ha : a ∈ discPoints E := hx
    exact (Set.ext_iff.mp h a).mpr ha

private theorem strict_ball_recenter {K Γ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (a b : K) (r : Γ)
    (hb : v (b - a) < r) : {x | v (x - b) < r} = {x | v (x - a) < r} := by
  have hab : v (a - b) < r := by rwa [v.map_sub_swap]
  ext x
  constructor
  · intro hx
    have h := (v.map_add (x - b) (b - a)).trans_lt (max_lt hx hb)
    simpa only [sub_add_sub_cancel, Set.mem_ofPred_eq] using h
  · intro hx
    have h := (v.map_add (x - a) (a - b)).trans_lt (max_lt hx hab)
    simpa only [sub_add_sub_cancel, Set.mem_ofPred_eq] using h

private theorem weak_ball_recenter {K Γ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (a b : K) (r : Γ)
    (hb : v (b - a) ≤ r) : {x | v (x - b) ≤ r} = {x | v (x - a) ≤ r} := by
  have hab : v (a - b) ≤ r := by rwa [v.map_sub_swap]
  ext x
  constructor
  · intro hx
    have h := (v.map_add (x - b) (b - a)).trans (max_le hx hb)
    simpa only [sub_add_sub_cancel, Set.mem_ofPred_eq] using h
  · intro hx
    have h := (v.map_add (x - a) (a - b)).trans (max_le hx hab)
    simpa only [sub_add_sub_cancel, Set.mem_ofPred_eq] using h

/-- Closed and open disc codes stay equal when their centres move inside
the same disc. The radii are genuine Gamma values, not named VF lifts. -/
theorem finitePolydiscNames_recenter {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) {n : ℕ}
    (closed : Fin n → Bool) (a b : Fin n → VF M) (δ : Fin n → Gamma M)
    (hb : ∀ i, b i ∈ discPoints (finitePolydiscNames closed a δ i)) :
    finitePolydiscNames closed b δ = finitePolydiscNames closed a δ := by
  funext i
  apply discPoints_injective
  let r := radiusRepresentative (δ i).val
  have hr : r ≠ 0 := fun hz => (δ i).property ((radiusRepresentative_zero_iff _).mp hz)
  have hval : vfValue r = (δ i).val := radiusRepresentative_value _
  have hfinite : finiteValue r hr = δ i := Subtype.ext hval
  cases hc : closed i with
  | false =>
    have hbi := hb i
    simp only [finitePolydiscNames, hc, Bool.false_eq_true, ite_false] at hbi ⊢
    rw [← hfinite, openDiscCode_points v hv _ r hr] at hbi ⊢
    rw [openDiscCode_points v hv _ r hr]
    exact strict_ball_recenter v (a i) (b i) (v r) hbi
  | true =>
    have hbi := hb i
    simp only [finitePolydiscNames, hc, ite_true] at hbi ⊢
    rw [← hval, closedDiscCode_points v hv _ r] at hbi ⊢
    rw [closedDiscCode_points v hv _ r]
    exact weak_ball_recenter v (a i) (b i) (v r) hbi

end DiamondIntegral.Section2
