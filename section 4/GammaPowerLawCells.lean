import «section 4».GammaDefinableMaps
import «section 4».GammaBaseExtension

/-! Definable power-law cells of an actual unary Gamma graph, and a
disjoint first-match refinement. Auxiliary coefficients are explicitly
named in Gamma, without introducing any RV representative as a parameter. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPowerLawCells
open GammaOrderLogic GammaBaseExtension GammaDefinableMaps

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem power_law_definable (B : Base (M := M)) {n : ℕ} (i j : Fin n)
    (p : ℤ) (q : ℕ) (c : Values.Gamma (M := M)) (hc : GammaDefinableClosureAtBase B c) :
    GammaDefinable B {z : Fin n → Values.Gamma (M := M) | z j ^ q = c * z i ^ p} :=
  equal_maps_definable B _ _
    (nat_power_definable B _ (projection_definable B j) q)
    (mul_definable B _ _ (constant_definable B c hc)
      (int_power_definable B _ (projection_definable B i) p))

def lawCell (D : Set (Values.Gamma (M := M))) (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (p : ℤ) (q : ℕ) (c : Values.Gamma (M := M)) : Set (Values.Gamma (M := M)) :=
  {x | x ∈ D ∧ T x ^ q = c * x ^ p}

theorem lawCell_definable (B : Base (M := M)) (D : Set (Values.Gamma (M := M)))
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1})
    (p : ℤ) (q : ℕ) (c : Values.Gamma (M := M)) (hc : GammaDefinableClosureAtBase B c) :
    GammaDefinableOverBase B (lawCell D T p q c) := by
  have hL := power_law_definable B (0 : Fin 2) 1 p q c hc
  have hI := GammaRelationLogic.inter_definable_base B _ _ hT hL
  have hS := GammaRelationLogic.preimage_definable_base B _ hI (![1, 0] : Fin 2 → Fin 2)
  have hE := GammaRelationLogic.exists_definable_base B _ hS
  apply (unary_definable_iff B (lawCell D T p q c)).mp
  convert hE using 1
  ext z
  change (z 0 ∈ D ∧ T (z 0) ^ q = c * z 0 ^ p) ↔
    ∃ y, (z 0 ∈ D ∧ T (z 0) = y) ∧ y ^ q = c * z 0 ^ p
  constructor
  · rintro ⟨hz, hl⟩
    exact ⟨T (z 0), ⟨hz, rfl⟩, hl⟩
  · rintro ⟨y, ⟨hz, hy⟩, hl⟩
    rw [← hy] at hl
    exact ⟨hz, hl⟩

theorem lawCells_definable_extend (B : Base (M := M)) {m : ℕ}
    (D : Set (Values.Gamma (M := M))) (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1})
    (p : Fin m → ℤ) (q : Fin m → ℕ) (c : Fin m → Values.Gamma (M := M)) :
    ∀ i, GammaDefinableOverBase (withGamma B (Set.range c)) (lawCell D T (p i) (q i) (c i)) := by
  intro i
  exact lawCell_definable (withGamma B (Set.range c)) D T
    (gammaRelation_extend B _ hT) (p i) (q i) (c i)
    (gammaName_extend B (Set.range c) (c i) ⟨i, rfl⟩)

def firstCell {m : ℕ} (C : Fin m → Set (Values.Gamma (M := M))) (i : Fin m) :
    Set (Values.Gamma (M := M)) := C i \ ⋃ j ∈ Finset.univ.filter (fun j => j < i), C j

theorem firstCell_definable (B : Base (M := M)) {m : ℕ}
    (C : Fin m → Set (Values.Gamma (M := M))) (hC : ∀ i, GammaDefinableOverBase B (C i))
    (i : Fin m) : GammaDefinableOverBase B (firstCell C i) :=
  (hC i).sdiff (finite_union_definable_base B _ C (fun j _ => hC j))

theorem firstCell_disjoint {m : ℕ} (C : Fin m → Set (Values.Gamma (M := M)))
    (i j : Fin m) (hij : i ≠ j) : Disjoint (firstCell C i) (firstCell C j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hxj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, hxi.1⟩⟩)
  · exact hxi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩, hxj.1⟩⟩)

theorem firstCell_cover {m : ℕ} (C : Fin m → Set (Values.Gamma (M := M)))
    (x : Values.Gamma (M := M)) : (∃ i, x ∈ C i) ↔ ∃ i, x ∈ firstCell C i := by
  constructor
  · rintro ⟨i, hi⟩
    let F := Finset.univ.filter (fun j => x ∈ C j)
    have hF : F.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    refine ⟨F.min' hF, (Finset.mem_filter.mp (F.min'_mem hF)).2, ?_⟩
    intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    have hjlt : j < F.min' hF := (Finset.mem_filter.mp hj).2
    exact (not_lt_of_ge (F.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxj⟩))) hjlt
  · rintro ⟨i, hi⟩
    exact ⟨i, hi.1⟩

theorem firstCell_sum {m : ℕ} (C : Fin m → Set (Values.Gamma (M := M)))
    (x : Values.Gamma (M := M)) :
    (∑ i : Fin m, if x ∈ firstCell C i then (1 : ℤ) else 0) =
      if ∃ i, x ∈ C i then 1 else 0 := by
  by_cases h : ∃ i, x ∈ C i
  · obtain ⟨j, hj⟩ := (firstCell_cover C x).mp h
    rw [ite_eq_left h]
    calc
      _ = (if x ∈ firstCell C j then (1 : ℤ) else 0) := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          apply ite_eq_right
          intro hi
          exact Set.disjoint_left.mp (firstCell_disjoint C i j hij) hi hj
        · intro hn
          exact False.elim (hn (Finset.mem_univ j))
      _ = 1 := ite_eq_left hj
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => h ⟨i, hi.1⟩)

end DiamondIntegral.Section4.GammaPowerLawCells
