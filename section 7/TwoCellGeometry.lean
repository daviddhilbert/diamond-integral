import «section 7».TwoCells

/-! Set-level geometry of `2`-cells, for Lemma 7.21 (`2:unit:contracted`).

* A balanced cell, with positioning function `ε` and paradigms `t₁`, `t₂`, is
  described in both coordinate orders (`balanced_mem_right`,
  `balanced_mem_left`):
  `(x, y) ∈ A ↔ x ∈ A₁ ∧ y - ε(x) ∈ t₂^♯` and, for `y ∈ A₂`,
  `(x, y) ∈ A ↔ x ∈ A₁ ∧ x - ε⁻¹(y) ∈ t₁^♯`. These are the translations
  `(x, y) ↦ (x, y - ε(x))` and `(x, y) ↦ (x - ε⁻¹(y), y)` of the paper's proof.
* A set whose fibres over its first projection all agree is a product
  (`eq_prod_of_fibres`). This is the product case of Lemma 7.21: constant
  positioning function, or the second kind of `2`-cell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section7.TwoCellGeometry
open DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {A : Set (VF M × VF M)} {ε : VF M → VF M} {t₁ t₂ : RVInfinity M}

/-- The inverse of the positioning function on the second projection. -/
def positionInv (A : Set (VF M × VF M)) (ε : VF M → VF M) : VF M → VF M := Function.invFunOn ε (first A)

theorem positionInv_mem (h : Balanced A ε t₁ t₂) {y : VF M} (hy : y ∈ second A) :
    positionInv A ε y ∈ first A :=
  Function.invFunOn_mem (h.bijective.surjOn hy)

theorem position_positionInv (h : Balanced A ε t₁ t₂) {y : VF M} (hy : y ∈ second A) :
    ε (positionInv A ε y) = y :=
  Function.invFunOn_eq (h.bijective.surjOn hy)

/-- **The order `21`:** `(x, y) ∈ A` iff `x ∈ A₁` and `y - ε(x) ∈ t₂^♯`. -/
theorem balanced_mem_right (h : Balanced A ε t₁ t₂) (x y : VF M) :
    (x, y) ∈ A ↔ x ∈ first A ∧ y - ε x ∈ sharpSet t₂ := by
  constructor
  · intro hxy
    have hx : x ∈ first A := ⟨(x, y), hxy, rfl⟩
    have hy : y ∈ fibre A x := hxy
    rw [h.fibre_eq x hx] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨hx, ?_⟩
    rw [add_sub_cancel_right]
    exact hs
  · rintro ⟨hx, hs⟩
    have hy : y ∈ fibre A x := by
      rw [h.fibre_eq x hx]
      exact ⟨y - ε x, hs, sub_add_cancel y (ε x)⟩
    exact hy

/-- **The order `12`:** for `y ∈ A₂`, `(x, y) ∈ A` iff `x ∈ A₁` and
`x - ε⁻¹(y) ∈ t₁^♯`. -/
theorem balanced_mem_left (h : Balanced A ε t₁ t₂) (x y : VF M) (hy : y ∈ second A) :
    (x, y) ∈ A ↔ x ∈ first A ∧ x - positionInv A ε y ∈ sharpSet t₁ := by
  have hinv := positionInv_mem h hy
  have hε := position_positionInv h hy
  constructor
  · intro hxy
    have hx : x ∈ first A := ⟨(x, y), hxy, rfl⟩
    have hmem : positionInv A ε y ∈ ε ⁻¹' fibre A x ∩ first A := by
      refine ⟨?_, hinv⟩
      change ε (positionInv A ε y) ∈ fibre A x
      rw [hε]
      exact hxy
    rw [h.preimage_eq x hx] at hmem
    obtain ⟨s, hs, hse⟩ := hmem
    refine ⟨hx, ?_⟩
    rw [← hse, sub_sub_cancel]
    exact hs
  · rintro ⟨hx, hs⟩
    have hmem : positionInv A ε y ∈ (x - ·) '' sharpSet t₁ :=
      ⟨x - positionInv A ε y, hs, sub_sub_cancel x _⟩
    rw [← h.preimage_eq x hx] at hmem
    have h1 : ε (positionInv A ε y) ∈ fibre A x := hmem.1
    rw [hε] at h1
    exact h1

omit [M ⊨ Axioms.ACVF] in
/-- A set whose fibres over its first projection all agree is a product. -/
theorem eq_prod_of_fibres (hfib : ∀ a ∈ first A, ∀ a' ∈ first A, fibre A a = fibre A a') {a₀ : VF M}
    (ha₀ : a₀ ∈ first A) : A = first A ×ˢ fibre A a₀ := by
  ext ⟨x, y⟩
  constructor
  · intro hxy
    have hx : x ∈ first A := ⟨(x, y), hxy, rfl⟩
    refine ⟨hx, ?_⟩
    have hy : y ∈ fibre A x := hxy
    rwa [hfib x hx a₀ ha₀] at hy
  · rintro ⟨hx, hy⟩
    have hy' : y ∈ fibre A x := by rwa [hfib x hx a₀ ha₀]
    exact hy'

/-- In a `2`-cell with constant positioning function, all fibres agree. -/
theorem fibres_eq_of_constant (hfib : ∀ a ∈ first A, fibre A a = (· + ε a) '' sharpSet t₂)
    (hconst : ∀ a ∈ first A, ∀ a' ∈ first A, ε a = ε a') :
    ∀ a ∈ first A, ∀ a' ∈ first A, fibre A a = fibre A a' := by
  intro a ha a' ha'
  rw [hfib a ha, hfib a' ha', hconst a ha a' ha']

end DiamondIntegral.Section7.TwoCellGeometry
