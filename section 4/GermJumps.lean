import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.BigOperators.Finprod

/-! One-sided germs and weighted germ jumps of subsets of a dense linear
order. For sets with finitely many jumps and germ dichotomy ("tame" sets)
the weighted jump sum is additive on disjoint unions, vanishes on finite
sets, and is transported by order-preserving and order-reversing bijections.
Purely order-theoretic; no model theory. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.GermJumps

variable {α : Type*} [LinearOrder α]

/-- `A` contains a right germ at `e`. -/
def RightIn (A : Set α) (e : α) : Prop := ∃ u, e < u ∧ Set.Ioo e u ⊆ A

/-- `A` contains a left germ at `e`. -/
def LeftIn (A : Set α) (e : α) : Prop := ∃ l, l < e ∧ Set.Ioo l e ⊆ A

/-- The germ jump of `A` at `e`: right germ indicator minus left germ indicator. -/
def jump (A : Set α) (e : α) : ℤ :=
  (if RightIn A e then 1 else 0) - (if LeftIn A e then 1 else 0)

/-- Finitely many jumps and germ dichotomy on both sides of every point. -/
structure Tame (A : Set α) : Prop where
  finite : (Function.support (jump A)).Finite
  right : ∀ e, RightIn A e ∨ RightIn Aᶜ e
  left : ∀ e, LeftIn A e ∨ LeftIn Aᶜ e

/-- The weighted jump sum. -/
def weightedJump (χ : α → ℤ) (A : Set α) : ℤ := ∑ᶠ e, jump A e * χ e

section Dense
variable [DenselyOrdered α]

theorem not_rightIn_both {A D : Set α} (hAD : Disjoint A D) (e : α)
    (hA : RightIn A e) (hD : RightIn D e) : False := by
  obtain ⟨u, hu, hAu⟩ := hA
  obtain ⟨u', hu', hDu⟩ := hD
  obtain ⟨x, hx1, hx2⟩ := exists_between (lt_min hu hu')
  exact Set.disjoint_left.mp hAD (hAu ⟨hx1, hx2.trans_le (min_le_left _ _)⟩)
    (hDu ⟨hx1, hx2.trans_le (min_le_right _ _)⟩)

theorem not_leftIn_both {A D : Set α} (hAD : Disjoint A D) (e : α)
    (hA : LeftIn A e) (hD : LeftIn D e) : False := by
  obtain ⟨l, hl, hAl⟩ := hA
  obtain ⟨l', hl', hDl⟩ := hD
  obtain ⟨x, hx1, hx2⟩ := exists_between (max_lt hl hl')
  exact Set.disjoint_left.mp hAD (hAl ⟨(le_max_left _ _).trans_lt hx1, hx2⟩)
    (hDl ⟨(le_max_right _ _).trans_lt hx1, hx2⟩)

theorem rightIn_union_iff {A D : Set α} (hA : ∀ e, RightIn A e ∨ RightIn Aᶜ e) (e : α) :
    RightIn (A ∪ D) e ↔ RightIn A e ∨ RightIn D e := by
  constructor
  · rintro ⟨u, hu, hAD⟩
    rcases hA e with h | ⟨u', hu', hc⟩
    · exact Or.inl h
    · refine Or.inr ⟨min u u', lt_min hu hu', fun x hx => ?_⟩
      have h1 := hAD ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩
      have h2 := hc ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
      exact h1.resolve_left h2
  · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
    · exact ⟨u, hu, h.trans Set.subset_union_left⟩
    · exact ⟨u, hu, h.trans Set.subset_union_right⟩

theorem leftIn_union_iff {A D : Set α} (hA : ∀ e, LeftIn A e ∨ LeftIn Aᶜ e) (e : α) :
    LeftIn (A ∪ D) e ↔ LeftIn A e ∨ LeftIn D e := by
  constructor
  · rintro ⟨l, hl, hAD⟩
    rcases hA e with h | ⟨l', hl', hc⟩
    · exact Or.inl h
    · refine Or.inr ⟨max l l', max_lt hl hl', fun x hx => ?_⟩
      have h1 := hAD ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩
      have h2 := hc ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩
      exact h1.resolve_left h2
  · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
    · exact ⟨l, hl, h.trans Set.subset_union_left⟩
    · exact ⟨l, hl, h.trans Set.subset_union_right⟩

theorem ite_or_eq_add {p q : Prop} (h : ¬ (p ∧ q)) :
    (if p ∨ q then (1 : ℤ) else 0) = (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- Jumps are additive on disjoint sets, given dichotomy for one of them. -/
theorem jump_union {A D : Set α} (hAD : Disjoint A D) (hA : Tame A) (e : α) :
    jump (A ∪ D) e = jump A e + jump D e := by
  unfold jump
  rw [if_congr (rightIn_union_iff hA.right e) rfl rfl, if_congr (leftIn_union_iff hA.left e) rfl rfl,
    ite_or_eq_add (fun h => not_rightIn_both hAD e h.1 h.2),
    ite_or_eq_add (fun h => not_leftIn_both hAD e h.1 h.2)]
  ring

theorem Tame.union {A D : Set α} (hAD : Disjoint A D) (hA : Tame A) (hD : Tame D) : Tame (A ∪ D) where
  finite := by
    apply (hA.finite.union hD.finite).subset
    intro e he
    rw [Function.mem_support, jump_union hAD hA e] at he
    by_contra hno
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hno
    exact he (by rw [hno.1, hno.2, add_zero])
  right e := by
    rcases hA.right e with h | ⟨u, hu, hc⟩
    · exact Or.inl ((rightIn_union_iff hA.right e).mpr (Or.inl h))
    rcases hD.right e with h' | ⟨u', hu', hc'⟩
    · exact Or.inl ((rightIn_union_iff hA.right e).mpr (Or.inr h'))
    refine Or.inr ⟨min u u', lt_min hu hu', fun x hx => ?_⟩
    rintro (h1 | h1)
    · exact hc ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩ h1
    · exact hc' ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩ h1
  left e := by
    rcases hA.left e with h | ⟨l, hl, hc⟩
    · exact Or.inl ((leftIn_union_iff hA.left e).mpr (Or.inl h))
    rcases hD.left e with h' | ⟨l', hl', hc'⟩
    · exact Or.inl ((leftIn_union_iff hA.left e).mpr (Or.inr h'))
    refine Or.inr ⟨max l l', max_lt hl hl', fun x hx => ?_⟩
    rintro (h1 | h1)
    · exact hc ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩ h1
    · exact hc' ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩ h1

theorem support_weighted_subset (χ : α → ℤ) (A : Set α) :
    Function.support (fun e => jump A e * χ e) ⊆ Function.support (jump A) := by
  intro e he h
  apply he
  change jump A e * χ e = 0
  rw [show jump A e = 0 from h, zero_mul]

theorem weightedJump_union (χ : α → ℤ) {A D : Set α} (hAD : Disjoint A D) (hA : Tame A) (hD : Tame D) :
    weightedJump χ (A ∪ D) = weightedJump χ A + weightedJump χ D := by
  unfold weightedJump
  rw [← finsum_add_distrib (hA.finite.subset (support_weighted_subset χ A))
    (hD.finite.subset (support_weighted_subset χ D))]
  apply finsum_congr
  intro e
  rw [jump_union hAD hA e, add_mul]

theorem weightedJump_empty (χ : α → ℤ) : weightedJump χ (∅ : Set α) = 0 := by
  unfold weightedJump
  have h : ∀ e, jump (∅ : Set α) e = 0 := by
    intro e
    have hr : ¬ RightIn (∅ : Set α) e := by
      rintro ⟨u, hu, h⟩
      obtain ⟨x, hx⟩ := exists_between hu
      exact h hx
    have hl : ¬ LeftIn (∅ : Set α) e := by
      rintro ⟨l, hl, h⟩
      obtain ⟨x, hx⟩ := exists_between hl
      exact h hx
    simp only [jump, hr, hl, ite_false, sub_self]
  simp only [h, zero_mul, finsum_zero]

end Dense

section Unbounded
variable [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α]

theorem tame_empty : Tame (∅ : Set α) where
  finite := by
    apply Set.finite_empty.subset
    intro e he
    exfalso
    apply he
    have hr : ¬ RightIn (∅ : Set α) e := by
      rintro ⟨u, hu, h⟩
      obtain ⟨x, hx⟩ := exists_between hu
      exact h hx
    have hl : ¬ LeftIn (∅ : Set α) e := by
      rintro ⟨l, hl, h⟩
      obtain ⟨x, hx⟩ := exists_between hl
      exact h hx
    simp only [jump, hr, hl, ite_false, sub_self]
  right e := by
    obtain ⟨u, hu⟩ := exists_gt e
    exact Or.inr ⟨u, hu, fun _ _ h => h⟩
  left e := by
    obtain ⟨l, hl⟩ := exists_lt e
    exact Or.inr ⟨l, hl, fun _ _ h => h⟩

/-- Finite sets have no germs, hence no jumps. -/
theorem jump_of_finite {A : Set α} (hA : A.Finite) (e : α) : jump A e = 0 := by
  have hr : ¬ RightIn A e := fun ⟨u, hu, h⟩ => (Set.Ioo_infinite hu) (hA.subset h)
  have hl : ¬ LeftIn A e := fun ⟨l, hl, h⟩ => (Set.Ioo_infinite hl) (hA.subset h)
  simp only [jump, hr, hl, ite_false, sub_self]

theorem weightedJump_of_finite (χ : α → ℤ) {A : Set α} (hA : A.Finite) : weightedJump χ A = 0 := by
  unfold weightedJump
  simp only [jump_of_finite hA, zero_mul, finsum_zero]

end Unbounded

section Transport
variable [DenselyOrdered α]

theorem rightIn_image_of_strictMono (f : α ≃ α) (hf : StrictMono f) (A : Set α) (e : α) :
    RightIn A e → RightIn (f '' A) (f e) := by
  rintro ⟨u, hu, h⟩
  refine ⟨f u, hf hu, fun y hy => ⟨f.symm y, h ⟨?_, ?_⟩, f.apply_symm_apply y⟩⟩
  · exact hf.lt_iff_lt.mp (by rw [f.apply_symm_apply]; exact hy.1)
  · exact hf.lt_iff_lt.mp (by rw [f.apply_symm_apply]; exact hy.2)

theorem leftIn_image_of_strictMono (f : α ≃ α) (hf : StrictMono f) (A : Set α) (e : α) :
    LeftIn A e → LeftIn (f '' A) (f e) := by
  rintro ⟨l, hl, h⟩
  refine ⟨f l, hf hl, fun y hy => ⟨f.symm y, h ⟨?_, ?_⟩, f.apply_symm_apply y⟩⟩
  · exact hf.lt_iff_lt.mp (by rw [f.apply_symm_apply]; exact hy.1)
  · exact hf.lt_iff_lt.mp (by rw [f.apply_symm_apply]; exact hy.2)

theorem rightIn_image_of_strictAnti (f : α ≃ α) (hf : StrictAnti f) (A : Set α) (e : α) :
    LeftIn A e → RightIn (f '' A) (f e) := by
  rintro ⟨l, hl, h⟩
  refine ⟨f l, hf hl, fun y hy => ⟨f.symm y, h ⟨?_, ?_⟩, f.apply_symm_apply y⟩⟩
  · exact hf.lt_iff_gt.mp (by rw [f.apply_symm_apply]; exact hy.2)
  · exact hf.lt_iff_gt.mp (by rw [f.apply_symm_apply]; exact hy.1)

theorem leftIn_image_of_strictAnti (f : α ≃ α) (hf : StrictAnti f) (A : Set α) (e : α) :
    RightIn A e → LeftIn (f '' A) (f e) := by
  rintro ⟨u, hu, h⟩
  refine ⟨f u, hf hu, fun y hy => ⟨f.symm y, h ⟨?_, ?_⟩, f.apply_symm_apply y⟩⟩
  · exact hf.lt_iff_gt.mp (by rw [f.apply_symm_apply]; exact hy.2)
  · exact hf.lt_iff_gt.mp (by rw [f.apply_symm_apply]; exact hy.1)

theorem symm_image_image (f : α ≃ α) (A : Set α) : f.symm '' (f '' A) = A := by
  rw [Set.image_image]
  simp only [Equiv.symm_apply_apply, Set.image_id']

theorem symm_strictMono {f : α ≃ α} (hf : StrictMono f) : StrictMono f.symm := by
  intro a b hab
  exact hf.lt_iff_lt.mp (by rw [f.apply_symm_apply, f.apply_symm_apply]; exact hab)

theorem symm_strictAnti {f : α ≃ α} (hf : StrictAnti f) : StrictAnti f.symm := by
  intro a b hab
  exact hf.lt_iff_gt.mp (by rw [f.apply_symm_apply, f.apply_symm_apply]; exact hab)

theorem rightIn_image_iff_of_strictMono (f : α ≃ α) (hf : StrictMono f) (A : Set α) (e : α) :
    RightIn (f '' A) (f e) ↔ RightIn A e := by
  refine ⟨fun h => ?_, rightIn_image_of_strictMono f hf A e⟩
  have h' := rightIn_image_of_strictMono f.symm (symm_strictMono hf) _ _ h
  rwa [symm_image_image, Equiv.symm_apply_apply] at h'

theorem leftIn_image_iff_of_strictMono (f : α ≃ α) (hf : StrictMono f) (A : Set α) (e : α) :
    LeftIn (f '' A) (f e) ↔ LeftIn A e := by
  refine ⟨fun h => ?_, leftIn_image_of_strictMono f hf A e⟩
  have h' := leftIn_image_of_strictMono f.symm (symm_strictMono hf) _ _ h
  rwa [symm_image_image, Equiv.symm_apply_apply] at h'

theorem rightIn_image_iff_of_strictAnti (f : α ≃ α) (hf : StrictAnti f) (A : Set α) (e : α) :
    RightIn (f '' A) (f e) ↔ LeftIn A e := by
  refine ⟨fun h => ?_, rightIn_image_of_strictAnti f hf A e⟩
  have h' := leftIn_image_of_strictAnti f.symm (symm_strictAnti hf) _ _ h
  rwa [symm_image_image, Equiv.symm_apply_apply] at h'

theorem leftIn_image_iff_of_strictAnti (f : α ≃ α) (hf : StrictAnti f) (A : Set α) (e : α) :
    LeftIn (f '' A) (f e) ↔ RightIn A e := by
  refine ⟨fun h => ?_, leftIn_image_of_strictAnti f hf A e⟩
  have h' := rightIn_image_of_strictAnti f.symm (symm_strictAnti hf) _ _ h
  rwa [symm_image_image, Equiv.symm_apply_apply] at h'

theorem image_compl (f : α ≃ α) (A : Set α) : f '' Aᶜ = (f '' A)ᶜ :=
  (Equiv.image_compl f A)

theorem jump_image_of_strictMono (f : α ≃ α) (hf : StrictMono f) (A : Set α) (e : α) :
    jump (f '' A) (f e) = jump A e := by
  simp only [jump, rightIn_image_iff_of_strictMono f hf, leftIn_image_iff_of_strictMono f hf]

theorem jump_image_of_strictAnti (f : α ≃ α) (hf : StrictAnti f) (A : Set α) (e : α) :
    jump (f '' A) (f e) = - jump A e := by
  simp only [jump, rightIn_image_iff_of_strictAnti f hf, leftIn_image_iff_of_strictAnti f hf]
  ring

theorem Tame.image_of_strictMono {A : Set α} (hA : Tame A) (f : α ≃ α) (hf : StrictMono f) :
    Tame (f '' A) where
  finite := by
    apply (hA.finite.image f).subset
    intro y hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [Function.mem_support] at hy ⊢
    rwa [← f.apply_symm_apply y, jump_image_of_strictMono f hf] at hy
  right e := by
    rw [← f.apply_symm_apply e, rightIn_image_iff_of_strictMono f hf, ← image_compl,
      rightIn_image_iff_of_strictMono f hf]
    exact hA.right _
  left e := by
    rw [← f.apply_symm_apply e, leftIn_image_iff_of_strictMono f hf, ← image_compl,
      leftIn_image_iff_of_strictMono f hf]
    exact hA.left _

theorem Tame.image_of_strictAnti {A : Set α} (hA : Tame A) (f : α ≃ α) (hf : StrictAnti f) :
    Tame (f '' A) where
  finite := by
    apply (hA.finite.image f).subset
    intro y hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [Function.mem_support] at hy ⊢
    rw [← f.apply_symm_apply y, jump_image_of_strictAnti f hf] at hy
    exact fun h => hy (by rw [h, neg_zero])
  right e := by
    rw [← f.apply_symm_apply e, rightIn_image_iff_of_strictAnti f hf, ← image_compl,
      rightIn_image_iff_of_strictAnti f hf]
    exact hA.left _
  left e := by
    rw [← f.apply_symm_apply e, leftIn_image_iff_of_strictAnti f hf, ← image_compl,
      leftIn_image_iff_of_strictAnti f hf]
    exact hA.right _

/-- Order-preserving transport with an invariant weight. -/
theorem weightedJump_image_of_strictMono (χ : α → ℤ) (A : Set α) (f : α ≃ α) (hf : StrictMono f)
    (hχ : ∀ e, χ (f e) = χ e) : weightedJump χ (f '' A) = weightedJump χ A := by
  unfold weightedJump
  rw [← finsum_comp_equiv f]
  apply finsum_congr
  intro e
  rw [jump_image_of_strictMono f hf, hχ]

/-- Order-reversing transport with an odd weight. -/
theorem weightedJump_image_of_strictAnti (χ : α → ℤ) (A : Set α) (f : α ≃ α) (hf : StrictAnti f)
    (hχ : ∀ e, χ (f e) = - χ e) : weightedJump χ (f '' A) = weightedJump χ A := by
  unfold weightedJump
  rw [← finsum_comp_equiv f]
  apply finsum_congr
  intro e
  rw [jump_image_of_strictAnti f hf, hχ]
  ring

end Transport

section Partitions
variable [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α]

/-- Finite disjoint partitions into tame pieces. -/
theorem weightedJump_biUnion (χ : α → ℤ) {ι : Type*} (s : Finset ι) (X : ι → Set α)
    (htame : ∀ i ∈ s, Tame (X i)) (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (X i) (X j)) :
    Tame (⋃ i ∈ s, X i) ∧ weightedJump χ (⋃ i ∈ s, X i) = ∑ i ∈ s, weightedJump χ (X i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty]
    exact ⟨tame_empty, weightedJump_empty χ⟩
  | insert a s ha ih =>
    have ih' := ih (fun i hi => htame i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    have hU : (⋃ i ∈ insert a s, X i) = X a ∪ ⋃ i ∈ s, X i := Finset.set_biUnion_insert a s X
    have hd : Disjoint (X a) (⋃ i ∈ s, X i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    have hta := htame a (Finset.mem_insert_self a s)
    rw [hU, Finset.sum_insert ha]
    exact ⟨hta.union hd ih'.1, by rw [weightedJump_union χ hd hta ih'.1, ih'.2]⟩

/-- Partition form: a set equal to a finite disjoint union of tame pieces. -/
theorem weightedJump_partition (χ : α → ℤ) {ι : Type*} [Fintype ι] (A : Set α) (X : ι → Set α)
    (htame : ∀ i, Tame (X i)) (hdisj : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hcover : A = ⋃ i, X i) : weightedJump χ A = ∑ i, weightedJump χ (X i) := by
  have h := weightedJump_biUnion χ Finset.univ X (fun i _ => htame i) (fun i _ j _ hij => hdisj i j hij)
  rw [hcover]
  simpa only [Finset.mem_univ, Set.iUnion_true] using h.2

end Partitions

end DiamondIntegral.Section4.GermJumps
