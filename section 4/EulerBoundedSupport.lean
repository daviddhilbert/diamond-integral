module

public import «section 4».EulerConvolution
public import Mathlib.Algebra.Ring.Subring.Basic

/-! Doubly bounded nonzero support, its coefficient criterion, and closure
under the proved Euler convolution. No Archimedean assumption is used. -/

@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4

variable {Γ : Type*} [LinearOrder Γ]

theorem stepEval_below (v : StepCoefficients Γ) (x : Γ)
    (h : ∀ a ∈ v.2.1.support ∪ v.2.2.support, x < a) : stepEval v x = v.1 := by
  have hp : v.2.1 x = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hx
    exact (lt_irrefl x) (h x (Finset.mem_union_left _ hx))
  have hq : jumpPrefix v.2.2 x = 0 := by
    unfold jumpPrefix Finsupp.sum
    apply Finset.sum_eq_zero
    intro a ha
    simp [not_lt_of_ge (le_of_lt (h a (Finset.mem_union_right _ ha)))]
  simp [stepEval, hp, hq]

theorem stepEval_above (v : StepCoefficients Γ) (x : Γ)
    (h : ∀ a ∈ v.2.1.support ∪ v.2.2.support, a < x) :
    stepEval v x = v.1 + coefficientSum v.2.2 := by
  have hp : v.2.1 x = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hx
    exact (lt_irrefl x) (h x (Finset.mem_union_left _ hx))
  have hq : jumpPrefix v.2.2 x = coefficientSum v.2.2 := by
    change v.2.2.sum (fun a n => if a < x then n else 0) = v.2.2.sum (fun _ n => n)
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro a ha
    simp [h a (Finset.mem_union_right _ ha)]
  simp [stepEval, hp, hq]

namespace EulerFunction
variable [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ] [AddCommGroup Γ]

def IsDoublyBounded {k : EulerKind} (f : EulerFunction k Γ) : Prop :=
  ∃ l u : Γ, ∀ x, f x ≠ 0 → l ≤ x ∧ x ≤ u

theorem ray_not_isDoublyBounded (k : EulerKind) (a : Γ) : ¬ IsDoublyBounded (ray k a) := by
  rintro ⟨_l, u, h⟩
  obtain ⟨x, hx⟩ := exists_gt (max a u)
  have hax : a < x := (le_max_left a u).trans_lt hx
  have hux : u < x := (le_max_right a u).trans_lt hx
  have hn : ray k a x ≠ 0 := by rw [ray_eval, ite_eq_left hax]; decide
  exact (not_lt_of_ge (h x hn).2) hux

theorem line_not_isDoublyBounded (k : EulerKind) : ¬ IsDoublyBounded (line (Γ := Γ) k) := by
  rintro ⟨_l, u, h⟩
  obtain ⟨x, hx⟩ := exists_gt u
  have hn : line k x ≠ 0 := by rw [line_eval]; decide
  exact (not_lt_of_ge (h x hn).2) hx

theorem isDoublyBounded_iff_coefficients (k : EulerKind) (f : EulerFunction k Γ) :
    IsDoublyBounded f ↔ ((coefficientEquiv k).symm f).1 = 0 ∧
      coefficientSum ((coefficientEquiv k).symm f).2.2 = 0 := by
  let v := (coefficientEquiv k).symm f
  let s := insert 0 (v.2.1.support ∪ v.2.2.support)
  have hs : s.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let l := s.min' hs
  let u := s.max' hs
  have hl (a : Γ) (ha : a ∈ v.2.1.support ∪ v.2.2.support) : l ≤ a :=
    Finset.min'_le s a (Finset.mem_insert_of_mem ha)
  have hu (a : Γ) (ha : a ∈ v.2.1.support ∪ v.2.2.support) : a ≤ u :=
    Finset.le_max' s a (Finset.mem_insert_of_mem ha)
  have heval (x : Γ) : stepEval v x = f x := coefficients_eval k f x
  change IsDoublyBounded f ↔ v.1 = 0 ∧ coefficientSum v.2.2 = 0
  constructor
  · rintro ⟨L, U, h⟩
    obtain ⟨x, hx⟩ := exists_lt (min L l)
    have hxL : x < L := (lt_min_iff.mp hx).1
    have hxl : x < l := (lt_min_iff.mp hx).2
    have hfx : f x = v.1 := (heval x).symm.trans
      (stepEval_below v x (fun a ha => hxl.trans_le (hl a ha)))
    have hc : v.1 = 0 := by
      by_contra hc
      have hnx : f x ≠ 0 := by rwa [hfx]
      exact (not_lt_of_ge (h x hnx).1) hxL
    obtain ⟨y, hy⟩ := exists_gt (max U u)
    have hUy : U < y := (max_lt_iff.mp hy).1
    have huy : u < y := (max_lt_iff.mp hy).2
    have hfy : f y = coefficientSum v.2.2 := by
      calc
        f y = stepEval v y := (heval y).symm
        _ = v.1 + coefficientSum v.2.2 := stepEval_above v y (fun a ha => (hu a ha).trans_lt huy)
        _ = coefficientSum v.2.2 := by rw [hc, zero_add]
    refine ⟨hc, ?_⟩
    by_contra hq
    have hny : f y ≠ 0 := by rwa [hfy]
    exact (not_lt_of_ge (h y hny).2) hUy
  · rintro ⟨hc, hq⟩
    refine ⟨l, u, ?_⟩
    intro x hnx
    constructor
    · by_contra hx
      have hxl : x < l := lt_of_not_ge hx
      have hfx : f x = 0 := (heval x).symm.trans
        ((stepEval_below v x (fun a ha => hxl.trans_le (hl a ha))).trans hc)
      exact hnx hfx
    · by_contra hx
      have hux : u < x := lt_of_not_ge hx
      have hfx : f x = 0 := by
        calc
          f x = stepEval v x := (heval x).symm
          _ = v.1 + coefficientSum v.2.2 := stepEval_above v x (fun a ha => (hu a ha).trans_lt hux)
          _ = 0 := by rw [hc, hq, add_zero]
      exact hnx hfx

theorem isDoublyBounded_zero (k : EulerKind) : IsDoublyBounded (0 : EulerFunction k Γ) := by
  refine ⟨0, 0, ?_⟩
  intro x hx
  exact False.elim (hx (eval_zero k x))

theorem isDoublyBounded_point (k : EulerKind) (a : Γ) : IsDoublyBounded (point k a) := by
  refine ⟨a, a, ?_⟩
  intro x hx
  have he : x = a := by
    by_contra h
    exact hx (by rw [point_eval, ite_eq_right h])
  subst x
  exact ⟨le_rfl, le_rfl⟩

theorem isDoublyBounded_one (k : EulerKind) : IsDoublyBounded (1 : EulerFunction k Γ) := by
  rw [← point_zero k]
  exact isDoublyBounded_point k 0

theorem IsDoublyBounded.neg {k : EulerKind} {f : EulerFunction k Γ} (hf : IsDoublyBounded f) :
    IsDoublyBounded (-f) := by
  obtain ⟨l, u, h⟩ := hf
  refine ⟨l, u, ?_⟩
  intro x hx
  apply h x
  intro hz
  exact hx (by rw [eval_neg, hz, neg_zero])

theorem IsDoublyBounded.add {k : EulerKind} {f g : EulerFunction k Γ}
    (hf : IsDoublyBounded f) (hg : IsDoublyBounded g) : IsDoublyBounded (f + g) := by
  obtain ⟨lf, uf, hf⟩ := hf
  obtain ⟨lg, ug, hg⟩ := hg
  refine ⟨min lf lg, max uf ug, ?_⟩
  intro x hx
  by_cases hfx : f x = 0
  · have hgx : g x ≠ 0 := by
      intro hz
      exact hx (by rw [eval_add, hfx, hz, add_zero])
    exact ⟨(min_le_right _ _).trans (hg x hgx).1, (hg x hgx).2.trans (le_max_right _ _)⟩
  · exact ⟨(min_le_left _ _).trans (hf x hfx).1, (hf x hfx).2.trans (le_max_left _ _)⟩

variable [IsOrderedAddMonoid Γ]

theorem convolution_support_witness (k : EulerKind) (f g : EulerFunction k Γ) (t : Γ)
    (ht : (f * g) t ≠ 0) : ∃ a, f a * g (t - a) ≠ 0 := by
  by_contra hn
  have hz : ∀ a, f a * g (t - a) = 0 := by
    intro a
    by_contra ha
    exact hn ⟨a, ha⟩
  have hi : pointwiseProduct k f (reflectAt k t g) = 0 := by
    apply eval_injective k
    funext a
    change pointwiseProduct k f (reflectAt k t g) a = (0 : EulerFunction k Γ) a
    rw [pointwiseProduct_eval, reflectAt_eval, hz a, eval_zero]
  have he := convolutionValue_eq_product k f g t
  rw [convolutionValue, hi, map_zero] at he
  exact ht he.symm

theorem IsDoublyBounded.mul {k : EulerKind} {f g : EulerFunction k Γ}
    (hf : IsDoublyBounded f) (hg : IsDoublyBounded g) : IsDoublyBounded (f * g) := by
  obtain ⟨lf, uf, hf⟩ := hf
  obtain ⟨lg, ug, hg⟩ := hg
  refine ⟨lf + lg, uf + ug, ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := convolution_support_witness k f g t ht
  have hfa : f a ≠ 0 := fun hz => ha (by rw [hz, zero_mul])
  have hga : g (t - a) ≠ 0 := fun hz => ha (by rw [hz, mul_zero])
  have hs : a + (t - a) = t := by abel
  constructor
  · exact (add_le_add (hf a hfa).1 (hg (t - a) hga).1).trans_eq hs
  · exact hs.symm.trans_le (add_le_add (hf a hfa).2 (hg (t - a) hga).2)

def boundedSubring (k : EulerKind) : Subring (EulerFunction k Γ) where
  carrier := IsDoublyBounded
  zero_mem' := isDoublyBounded_zero k
  one_mem' := isDoublyBounded_one k
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  neg_mem' := fun hf => hf.neg

end EulerFunction
end DiamondIntegral.Section4
