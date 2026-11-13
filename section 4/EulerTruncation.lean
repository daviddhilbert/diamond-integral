module

public import «section 4».EulerBoundedComparison

/-! Unary stabilization of the bounded Euler characteristic: integrate the
actual function on a sufficiently large closed symmetric interval using
geometric Euler characteristic. The proof works in non-Archimedean Gamma. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ]
  [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def closedInterval (k : EulerKind) (a b : Γ) : EulerFunction k Γ :=
  if a ≤ b then ray k a - ray k b + point k a else 0

theorem closedInterval_eval (k : EulerKind) (a b x : Γ) :
    closedInterval k a b x = if a ≤ x ∧ x ≤ b then 1 else 0 := by
  by_cases hab : a ≤ b
  · rw [closedInterval, ite_eq_left hab]
    simp only [eval_add, eval_sub, ray_eval, point_eval]
    rcases lt_trichotomy x a with hx | hx | hx
    · have hbx : ¬ b < x := not_lt_of_ge (hx.le.trans hab)
      simp [not_le_of_gt hx, not_lt_of_ge hx.le, ne_of_lt hx, hbx]
    · subst x
      simp [hab, not_lt_of_ge hab]
    · by_cases hxb : x ≤ b
      · simp [hx, hx.le, hxb, not_lt_of_ge hxb, ne_of_gt hx]
      · simp [hx, hx.le, hxb, lt_of_not_ge hxb, ne_of_gt hx]
  · rw [closedInterval, ite_eq_right hab, eval_zero]
    have he : ¬ (a ≤ x ∧ x ≤ b) := fun h => hab (h.1.trans h.2)
    simp [he]

theorem totalEuler_closedInterval (k : EulerKind) (a b : Γ) :
    totalEuler k (closedInterval k a b) = if a ≤ b then 1 else 0 := by
  by_cases hab : a ≤ b <;>
    simp [closedInterval, hab, map_add, map_sub, totalEuler_ray, totalEuler_point]

def truncate (k : EulerKind) (a b : Γ) : EulerFunction k Γ →+ EulerFunction k Γ where
  toFun f := pointwiseProduct k f (closedInterval k a b)
  map_zero' := pointwiseProduct_zero_left k _
  map_add' f g := pointwiseProduct_add_left k f g _

theorem truncate_eval (k : EulerKind) (a b : Γ) (f : EulerFunction k Γ) (x : Γ) :
    truncate k a b f x = if a ≤ x ∧ x ≤ b then f x else 0 := by
  change pointwiseProduct k f (closedInterval k a b) x = _
  rw [pointwiseProduct_eval, closedInterval_eval]
  split_ifs <;> simp

theorem truncate_line (k : EulerKind) (a b : Γ) :
    truncate k a b (line k) = closedInterval k a b := pointwiseProduct_line k _

theorem truncate_point (k : EulerKind) (a b c : Γ) (ha : a ≤ c) (hb : c ≤ b) :
    truncate k a b (point k c) = point k c := by
  change pointwiseProduct k (point k c) (closedInterval k a b) = _
  rw [pointwiseProduct_point, closedInterval_eval, ite_eq_left ⟨ha, hb⟩, one_zsmul]

theorem truncate_ray (k : EulerKind) (a b c : Γ) (ha : a ≤ c) (hb : c < b) :
    truncate k a b (ray k c) = ray k c - ray k b := by
  apply eval_injective k
  funext x
  change truncate k a b (ray k c) x = (ray k c - ray k b) x
  rw [truncate_eval, eval_sub, ray_eval, ray_eval]
  by_cases hcx : c < x
  · have hax : a ≤ x := ha.trans hcx.le
    by_cases hxb : x ≤ b
    · simp [hcx, hax, hxb, not_lt_of_ge hxb]
    · simp [hcx, hxb, lt_of_not_ge hxb]
  · have hbx : ¬ b < x := fun h => hcx (hb.trans h)
    simp [hcx, hbx]

theorem totalEuler_truncate_coefficients (k : EulerKind) (a b : Γ) (hab : a ≤ b)
    (v : StepCoefficients Γ)
    (hv : ∀ c ∈ v.2.1.support ∪ v.2.2.support, a ≤ c ∧ c < b) :
    totalEuler k (truncate k a b (linearCombination k v)) = v.1 + coefficientSum v.2.1 := by
  let T := (totalEuler k).toAddMonoidHom.comp (truncate k a b)
  have hline : T (line k) = 1 := by
    change totalEuler k (truncate k a b (line k)) = 1
    rw [truncate_line, totalEuler_closedInterval, ite_eq_left hab]
  have hp : v.2.1.sum (fun c n => T (n • point k c)) = coefficientSum v.2.1 := by
    unfold Finsupp.sum coefficientSum
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨hl, hu⟩ := hv c (Finset.mem_union_left _ hc)
    change T (v.2.1 c • point k c) = v.2.1 c
    rw [map_zsmul]
    change v.2.1 c • totalEuler k (truncate k a b (point k c)) = _
    rw [truncate_point k a b c hl hu.le, totalEuler_point]
    simp
  have hq : v.2.2.sum (fun c n => T (n • ray k c)) = 0 := by
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro c hc
    obtain ⟨hl, hu⟩ := hv c (Finset.mem_union_right _ hc)
    change T (v.2.2 c • ray k c) = 0
    rw [map_zsmul]
    change v.2.2 c • totalEuler k (truncate k a b (ray k c)) = 0
    rw [truncate_ray k a b c hl hu, map_sub, totalEuler_ray, totalEuler_ray, sub_self,
      zsmul_zero]
  change T (linearCombination k v) = _
  simp only [linearCombination, map_add, Finsupp.sum, map_sum]
  change T (v.1 • line k) + v.2.1.sum (fun c n => T (n • point k c)) +
    v.2.2.sum (fun c n => T (n • ray k c)) = _
  rw [hp, hq, add_zero, map_zsmul, hline]
  simp

variable [IsOrderedAddMonoid Γ]

theorem boundedEuler_stabilization (f : EulerFunction EulerKind.geometric Γ) :
    ∃ R : Γ, 0 < R ∧ ∀ r, R ≤ r →
      totalEuler EulerKind.geometric (truncate EulerKind.geometric (-r) r f) =
        totalEuler EulerKind.bounded (changeKind EulerKind.geometric EulerKind.bounded f) := by
  obtain ⟨v, hv⟩ := generator_expansion EulerKind.geometric f
  let S := v.2.1.support ∪ v.2.2.support
  let F := insert 0 (S ∪ S.image (fun x => -x))
  have hF : F.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨R, hR⟩ := exists_gt (F.max' hF)
  have h0 : 0 < R := (Finset.le_max' F 0 (Finset.mem_insert_self _ _)).trans_lt hR
  refine ⟨R, h0, ?_⟩
  intro r hr
  have hr0 : 0 ≤ r := h0.le.trans hr
  have hcut (c : Γ) (hc : c ∈ S) : -r ≤ c ∧ c < r := by
    have hcF : c ∈ F := Finset.mem_insert_of_mem (Finset.mem_union_left _ hc)
    have hnF : -c ∈ F := Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩))
    have hu : c < r := ((Finset.le_max' F c hcF).trans_lt hR).trans_le hr
    have hn : -c < r := ((Finset.le_max' F (-c) hnF).trans_lt hR).trans_le hr
    exact ⟨(neg_lt.mp hn).le, hu⟩
  rw [hv, totalEuler_truncate_coefficients EulerKind.geometric (-r) r
    (by exact (neg_nonpos.mpr hr0).trans hr0) v hcut]
  have hchange : changeKind EulerKind.geometric EulerKind.bounded (linearCombination EulerKind.geometric v) =
      ofCoefficients EulerKind.bounded v := by
    rw [← ofCoefficients_eq_linearCombination]
    change (coefficientEquiv EulerKind.bounded)
      ((coefficientEquiv EulerKind.geometric).symm ((coefficientEquiv EulerKind.geometric) v)) = _
    rw [AddEquiv.symm_apply_apply]
    rfl
  rw [hchange, totalEuler_ofCoefficients]
  simp [EulerKind.lineValue, EulerKind.rayValue]

end DiamondIntegral.Section4.EulerFunction
