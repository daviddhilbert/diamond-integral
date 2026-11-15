module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

/-!
# Value-induced consolidation of a finite rectangle cover

This is the finite assembly step in the approved proof of Lemma 5.12.
Different rectangles may have overlapping Gamma supports. Partition the
*value image*, using a fixed active value and the membership pattern in all
Gamma supports, and unite the corresponding residue factors on each piece.

This file proves the set-theoretic assembly. It does not assert the ACVF
definability or original-ground parameter descent of the resulting data.
-/

set_option autoImplicit false
@[expose] public section

namespace DiamondIntegral.Section5
noncomputable section
open Set

variable {I R Y V G : Type*}

def rectangleValueCell (a : R → V) (v : Y → G) (X : Set (R × Y))
    (supports : I → Set G) (β : V) (s : Finset I) : Set (V × G) :=
  {q | q ∈ Prod.map a v '' X ∧ q.1 = β ∧ ∀ i, q.2 ∈ supports i ↔ i ∈ s}

def rectangleResidueCell (a : R → V) (residues : I → Set R)
    (β : V) (s : Finset I) : Set R :=
  {r | a r = β ∧ ∃ i ∈ s, r ∈ residues i}

def rectangleGammaCell (a : R → V) (v : Y → G) (X : Set (R × Y))
    (supports : I → Set G) (β : V) (s : Finset I) : Set G :=
  {γ | (β, γ) ∈ rectangleValueCell a v X supports β s}

/-- Every resulting source piece is cut out by values alone, and becomes
a single rectangle, even when the original Gamma supports overlap. -/
theorem valueInduced_rectangle_identity
    (a : R → V) (v : Y → G) (X : Set (R × Y))
    (residues : I → Set R) (supports : I → Set G)
    (hX : ∀ r y, (r, y) ∈ X ↔ ∃ i, r ∈ residues i ∧ v y ∈ supports i)
    (β : V) (s : Finset I) :
    X ∩ Prod.map a v ⁻¹' rectangleValueCell a v X supports β s =
      (rectangleResidueCell a residues β s).prod
        (v ⁻¹' rectangleGammaCell a v X supports β s) := by
  classical
  ext ⟨r, y⟩
  constructor
  · rintro ⟨hx, hq⟩
    obtain ⟨i, hi, hg⟩ := (hX r y).mp hx
    refine ⟨⟨hq.2.1, i, (hq.2.2 i).mp hg, hi⟩, ?_⟩
    change (β, v y) ∈ rectangleValueCell a v X supports β s
    change (a r, v y) ∈ rectangleValueCell a v X supports β s at hq
    have ha : a r = β := hq.2.1
    simpa only [ha] using hq
  · rintro ⟨⟨ha, i, hs, hr⟩, hγ⟩
    have hg : v y ∈ supports i := (hγ.2.2 i).mpr hs
    have hx := (hX r y).mpr ⟨i, hr, hg⟩
    refine ⟨hx, ?_⟩
    change (a r, v y) ∈ rectangleValueCell a v X supports β s
    change (β, v y) ∈ rectangleValueCell a v X supports β s at hγ
    simpa only [ha] using hγ

theorem rectangleValueCells_disjoint
    (a : R → V) (v : Y → G) (X : Set (R × Y)) (supports : I → Set G)
    {β β' : V} {s s' : Finset I} (hne : (β, s) ≠ (β', s')) :
    Disjoint (rectangleValueCell a v X supports β s)
      (rectangleValueCell a v X supports β' s') := by
  classical
  apply Set.disjoint_left.mpr
  intro q h h'
  apply hne
  apply Prod.ext
  · exact h.2.1.symm.trans h'.2.1
  · exact Finset.ext fun i => (h.2.2 i).symm.trans (h'.2.2 i)

/-- The active values used by the assembly remain finite. -/
theorem rectangle_active_values_finite
    [Fintype I]
    (a : R → V) (v : Y → G) (X : Set (R × Y))
    (residues : I → Set R) (supports : I → Set G)
    (hX : ∀ r y, (r, y) ∈ X ↔ ∃ i, r ∈ residues i ∧ v y ∈ supports i)
    (hfinite : ∀ i, (a '' residues i).Finite) :
    ((a ∘ Prod.fst) '' X).Finite := by
  apply (Set.finite_iUnion hfinite).subset
  rintro β ⟨⟨r, y⟩, hx, rfl⟩
  obtain ⟨i, hr, _⟩ := (hX r y).mp hx
  exact Set.mem_iUnion.mpr ⟨i, r, hr, rfl⟩

/-- A genuinely finite partition of the original value support, including
empty cells. Nonempty cells have a fixed active value and a product source. -/
theorem finite_valueInduced_rectangle_partition
    [Fintype I]
    (a : R → V) (v : Y → G) (X : Set (R × Y))
    (residues : I → Set R) (supports : I → Set G)
    (hX : ∀ r y, (r, y) ∈ X ↔ ∃ i, r ∈ residues i ∧ v y ∈ supports i)
    (hfinite : ∀ i, (a '' residues i).Finite) :
    ∃ N : ℕ, ∃ (β : Fin N → V) (s : Fin N → Finset I),
      (∀ j k, j ≠ k →
        Disjoint (rectangleValueCell a v X supports (β j) (s j))
          (rectangleValueCell a v X supports (β k) (s k))) ∧
      (∀ q, q ∈ Prod.map a v '' X ↔
        ∃ j, q ∈ rectangleValueCell a v X supports (β j) (s j)) ∧
      (∀ j, X ∩ Prod.map a v ⁻¹' rectangleValueCell a v X supports (β j) (s j) =
        (rectangleResidueCell a residues (β j) (s j)).prod
          (v ⁻¹' rectangleGammaCell a v X supports (β j) (s j))) ∧
      (∀ j, a '' rectangleResidueCell a residues (β j) (s j) ⊆ {β j}) ∧
      (∀ j, β j ∈ (a ∘ Prod.fst) '' X) := by
  classical
  let H := (a ∘ Prod.fst) '' X
  have hH : H.Finite := rectangle_active_values_finite a v X residues supports hX hfinite
  let : Fintype H := hH.fintype
  let J := H × Finset I
  let : Fintype J := inferInstanceAs (Fintype (H × Finset I))
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun j => (e j).1.val, fun j => (e j).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j k hne
    apply rectangleValueCells_disjoint
    intro he
    apply hne
    apply e.injective
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun p : V × Finset I => p.1) he)
    · exact congrArg (fun p : V × Finset I => p.2) he
  · intro q
    constructor
    · rintro hq
      have hβ : q.1 ∈ H := by
        obtain ⟨⟨r, y⟩, hx, he⟩ := hq
        exact ⟨(r, y), hx, congrArg Prod.fst he⟩
      let s : Finset I := Finset.univ.filter fun i => q.2 ∈ supports i
      obtain ⟨j, hj⟩ := e.surjective (⟨q.1, hβ⟩, s)
      refine ⟨j, ?_⟩
      change q ∈ rectangleValueCell a v X supports (e j).1.val (e j).2
      rw [hj]
      refine ⟨hq, rfl, ?_⟩
      intro i
      simp [s]
    · rintro ⟨j, hj⟩
      exact hj.1
  · intro j
    exact valueInduced_rectangle_identity a v X residues supports hX _ _
  · intro j β' hβ'
    obtain ⟨r, hr, rfl⟩ := hβ'
    exact hr.1
  · intro j
    exact (e j).1.property

end
end DiamondIntegral.Section5
