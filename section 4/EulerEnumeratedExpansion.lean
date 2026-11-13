module

public import «section 4».EulerGerms

/-! Canonical point-and-ray expansion using any finite bijective indexing
of the actual breakpoint set. Germ differences give the weights, and
inactive indices can subsequently be extended by zero. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

theorem finsupp_sum_eq_enumerated {α ι A : Type*} [AddCommGroup A]
    (S : Finset α) (s : Finset ι) (t : ι → α) (hb : Set.BijOn t (s : Set ι) (S : Set α))
    (p : α →₀ ℤ) (hp : p.support ⊆ S) (g : α → A) :
    p.sum (fun a n => n • g a) = ∑ i ∈ s, p (t i) • g (t i) := by
  rw [Finsupp.sum_of_support_subset p hp (fun a n => n • g a) (fun _ _ => zero_smul _ _)]
  symm
  apply Finset.sum_bij (fun i _ => t i)
  · exact fun i hi => hb.mapsTo hi
  · exact fun i hi j hj hij => hb.injOn hi hj hij
  · intro a ha
    obtain ⟨i, hi, he⟩ := hb.surjOn ha
    exact ⟨i, hi, he⟩
  · exact fun _ _ => rfl

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ]
  [AddCommGroup Γ]

theorem expansion_of_finite_enumeration {ι : Type*} (k : EulerKind) (f : EulerFunction k Γ)
    (s : Finset ι) (t : ι → Γ) (hb : Set.BijOn t (s : Set ι) (breakpoints k f : Set Γ)) :
    f = tailValue k f • line k +
      (∑ i ∈ s, (f (t i) - leftValue k f (t i)) • point k (t i)) +
      ∑ i ∈ s, (rightValue k f (t i) - leftValue k f (t i)) • ray k (t i) := by
  let v := (coefficientEquiv k).symm f
  have he : linearCombination k v = f := by
    rw [← ofCoefficients_eq_linearCombination]
    exact (coefficientEquiv k).apply_symm_apply f
  have hp : v.2.1.sum (fun a n => n • point k a) = ∑ i ∈ s, v.2.1 (t i) • point k (t i) :=
    finsupp_sum_eq_enumerated (breakpoints k f) s t hb v.2.1 Finset.subset_union_left (point k)
  have hq : v.2.2.sum (fun a n => n • ray k a) = ∑ i ∈ s, v.2.2 (t i) • ray k (t i) :=
    finsupp_sum_eq_enumerated (breakpoints k f) s t hb v.2.2 Finset.subset_union_right (ray k)
  have hpv (a : Γ) : v.2.1 a = f a - leftValue k f a := pointCoefficient_eq k f a
  have hqv (a : Γ) : v.2.2 a = rightValue k f a - leftValue k f a := rayCoefficient_eq k f a
  calc
    f = linearCombination k v := he.symm
    _ = tailValue k f • line k +
        (∑ i ∈ s, (f (t i) - leftValue k f (t i)) • point k (t i)) +
        ∑ i ∈ s, (rightValue k f (t i) - leftValue k f (t i)) • ray k (t i) := by
      unfold linearCombination
      rw [hp, hq]
      simp_rw [hpv, hqv]
      rfl

theorem coefficient_expansion_of_finite_enumeration {ι : Type*} (k : EulerKind) (f : EulerFunction k Γ)
    (s : Finset ι) (t : ι → Γ) (hb : Set.BijOn t (s : Set ι) (breakpoints k f : Set Γ)) :
    f = tailValue k f • line k +
      (∑ i ∈ s, ((coefficientEquiv k).symm f).2.1 (t i) • point k (t i)) +
      ∑ i ∈ s, ((coefficientEquiv k).symm f).2.2 (t i) • ray k (t i) := by
  simpa only [← pointCoefficient_eq, ← rayCoefficient_eq] using expansion_of_finite_enumeration k f s t hb

end DiamondIntegral.Section4.EulerFunction
