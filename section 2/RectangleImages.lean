import Mathlib

/-! Coordinate-chain image lemmas. They are purely set-theoretic: the
family can subsequently be instantiated with actual ACVF open discs.
No result from the T-convex setting is imported. -/

namespace DiamondIntegral.Section2
variable {α β : Type*} {n : ℕ}

def coordinateLineImage (D : Fin n → Set α) (f : (Fin n → α) → β)
    (a : Fin n → α) (i : Fin n) : Set β :=
  (fun x => f (Function.update a i x)) '' D i

/-- Finite rectangles are connected by single-coordinate replacements. -/
theorem rectangle_induction (D : Fin n → Set α) (P : (Fin n → α) → Prop)
    (a : Fin n → α) (ha : ∀ j, a j ∈ D j) (hPa : P a)
    (hstep : ∀ b, (∀ j, b j ∈ D j) → P b → ∀ i x, x ∈ D i →
      P (Function.update b i x)) :
    ∀ b, (∀ j, b j ∈ D j) → P b := by
  classical
  intro b hb
  let v (s : Finset (Fin n)) : Fin n → α := fun j => if j ∈ s then b j else a j
  have hvD (s : Finset (Fin n)) : ∀ j, v s j ∈ D j := by
    intro j
    by_cases hj : j ∈ s
    · simpa only [v, ite_eq_left hj] using hb j
    · simpa only [v, ite_eq_right hj] using ha j
  have hvP (s : Finset (Fin n)) : P (v s) := by
    induction s using Finset.induction_on with
    | empty => simpa only [v, Finset.notMem_empty, ite_false] using hPa
    | @insert i s _hi ih =>
      have hh := hstep (v s) (hvD s) ih i (b i) (hb i)
      have he : v (insert i s) = Function.update (v s) i (b i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [v]
        · simp [v, hj]
      rwa [he]
  simpa only [v, Finset.mem_univ, ite_true] using hvP Finset.univ

/-- If each coordinate-line image is a point or belongs to a nested family,
any two distinct image values lie together in one member inside the image. -/
theorem rectangle_image_pair (D : Fin n → Set α) (f : (Fin n → α) → β)
    (F : Set (Set β))
    (hnest : ∀ B ∈ F, ∀ C ∈ F, (B ∩ C).Nonempty → B ⊆ C ∨ C ⊆ B)
    (hlines : ∀ a, (∀ j, a j ∈ D j) → ∀ i,
      (coordinateLineImage D f a i).Subsingleton ∨ coordinateLineImage D f a i ∈ F)
    (p q : β) (hp : p ∈ f '' {a | ∀ j, a j ∈ D j})
    (hq : q ∈ f '' {a | ∀ j, a j ∈ D j}) (hpq : p ≠ q) :
    ∃ B ∈ F, B ⊆ f '' {a | ∀ j, a j ∈ D j} ∧ p ∈ B ∧ q ∈ B := by
  classical
  obtain ⟨a, ha, hpa⟩ := hp
  obtain ⟨b, hb, hqb⟩ := hq
  let P (c : Fin n → α) := f c = p ∨
    ∃ B ∈ F, B ⊆ f '' {a | ∀ j, a j ∈ D j} ∧ p ∈ B ∧ f c ∈ B
  have hstep (c : Fin n → α) (hc : ∀ j, c j ∈ D j) (hPc : P c)
      (i : Fin n) (x : α) (hx : x ∈ D i) : P (Function.update c i x) := by
    let L := coordinateLineImage D f c i
    have hcur : f c ∈ L := ⟨c i, hc i, by simp⟩
    have hnew : f (Function.update c i x) ∈ L := ⟨x, hx, rfl⟩
    rcases hlines c hc i with hsmall | hL
    · have he := hsmall hnew hcur
      simpa only [P, he] using hPc
    have hLC : L ⊆ f '' {a | ∀ j, a j ∈ D j} := by
      rintro y ⟨z, hz, rfl⟩
      refine ⟨Function.update c i z, ?_, rfl⟩
      intro j
      by_cases hji : j = i
      · subst j; simpa using hz
      · simpa only [Function.update_of_ne hji] using hc j
    right
    rcases hPc with he | ⟨B, hB, hBC, hpB, hcB⟩
    · exact ⟨L, hL, hLC, he ▸ hcur, hnew⟩
    · rcases hnest B hB L hL ⟨f c, hcB, hcur⟩ with hBL | hLB
      · exact ⟨L, hL, hLC, hBL hpB, hnew⟩
      · exact ⟨B, hB, hBC, hpB, hLB hnew⟩
  have hbP := rectangle_induction D P a ha (Or.inl hpa) hstep b hb
  rcases hbP with he | ⟨B, hB, hBC, hpB, hbB⟩
  · exact (hpq (he.symm.trans hqb)).elim
  · exact ⟨B, hB, hBC, hpB, hqb ▸ hbB⟩

/-- A maximal family member containing one image value contains the whole
rectangle image. This is the maximal-open-disc step of the approved proof. -/
theorem rectangle_image_eq_maximal (D : Fin n → Set α) (f : (Fin n → α) → β)
    (F : Set (Set β))
    (hnest : ∀ B ∈ F, ∀ C ∈ F, (B ∩ C).Nonempty → B ⊆ C ∨ C ⊆ B)
    (hlines : ∀ a, (∀ j, a j ∈ D j) → ∀ i,
      (coordinateLineImage D f a i).Subsingleton ∨ coordinateLineImage D f a i ∈ F)
    (B : Set β) (hB : B ∈ F) (hBC : B ⊆ f '' {a | ∀ j, a j ∈ D j})
    (hmax : ∀ C ∈ F, C ⊆ f '' {a | ∀ j, a j ∈ D j} → B ⊆ C → C ⊆ B)
    (p : β) (hpB : p ∈ B) : f '' {a | ∀ j, a j ∈ D j} = B := by
  apply Set.Subset.antisymm ?_ hBC
  intro q hq
  by_cases hpq : p = q
  · exact hpq ▸ hpB
  obtain ⟨C, hC, hCI, hpC, hqC⟩ :=
    rectangle_image_pair D f F hnest hlines p q (hBC hpB) hq hpq
  rcases hnest B hB C hC ⟨p, hpB, hpC⟩ with h | h
  · exact hmax C hC hCI h hqC
  · exact h hqC

/-- A coordinate chain from a point inside a set to a point outside it
has an exit along a single coordinate of the same rectangle. -/
theorem rectangle_coordinate_exit (D : Fin n → Set α) (A : Set (Fin n → α))
    (a b : Fin n → α) (ha : ∀ j, a j ∈ D j) (hb : ∀ j, b j ∈ D j)
    (haA : a ∈ A) (hbA : b ∉ A) :
    ∃ c : Fin n → α, (∀ j, c j ∈ D j) ∧ c ∈ A ∧
      ∃ i x, x ∈ D i ∧ Function.update c i x ∉ A := by
  classical
  by_contra hn
  have hstep (c : Fin n → α) (hc : ∀ j, c j ∈ D j) (hcA : c ∈ A)
      (i : Fin n) (x : α) (hx : x ∈ D i) : Function.update c i x ∈ A := by
    by_contra hbad
    exact hn ⟨c, hc, hcA, i, x, hx, hbad⟩
  exact hbA (rectangle_induction D (fun c => c ∈ A) a ha haA hstep b hb)

end DiamondIntegral.Section2
