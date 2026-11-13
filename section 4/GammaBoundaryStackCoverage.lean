import «section 4».GammaBoundaryStackFamily
import «section 4».FiniteOrderComponents

/-! The finite boundary stack family covers the original definable set.
For each actual fibre, finite order supplies the neighbouring boundary
points or missing endpoints. Endpoint labels come from the original-base
graph partition; no new endpoint or RV parameters are named. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryStackCoverage
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints GammaBoundaryStackFamily
open GammaBoundaryStacks GammaBoundaryStackBases GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem boundary_fibre_finite (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (y : Fin n → Values.Gamma (M := M)) :
    {x | Fin.cons x y ∈ GammaFamilyBoundary.Boundary R}.Finite := by
  apply (Set.finite_range (fun i : Fin P.size => endpoint P i y)).subset
  intro x hx
  obtain ⟨i, hi, he⟩ := exists_endpoint P y x hx
  exact ⟨i, he⟩

theorem cover_cons (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R))
    (y : Fin n → Values.Gamma (M := M)) (x : Values.Gamma (M := M)) (hx : Fin.cons x y ∈ R) :
    ∃ label : Label P.size, Fin.cons x y ∈ stack R P label := by
  let hfin := boundary_fibre_finite R P y
  let A := hfin.toFinset
  have hmem (t : Values.Gamma (M := M)) : t ∈ A ↔ Fin.cons t y ∈ GammaFamilyBoundary.Boundary R := hfin.mem_toFinset
  rcases FiniteOrderComponents.component_cover A x with hpoint | hempty | hlower | hupper | hband
  · obtain ⟨i, hi, he⟩ := exists_endpoint P y x ((hmem x).mp hpoint)
    refine ⟨.inl i, ?_⟩
    change y ∈ pointBase R (P.domain i) (endpoint P i) ∧ x = endpoint P i y
    refine ⟨(mem_fibreBase _ y).mpr ⟨x, hx, hi, he.symm⟩, he.symm⟩
  · refine ⟨.inr (.inr (.inr (.inr ()))), ?_⟩
    change y ∈ lineBase R Set.univ
    refine ⟨Set.mem_univ y, (mem_activeBase R (lineCell Set.univ) y).mpr ⟨⟨x, hx, Set.mem_univ y⟩, ?_⟩⟩
    intro t _ ht
    have htA := (hmem t).mpr ht
    rw [hempty] at htA
    exact Finset.notMem_empty t htA
  · obtain ⟨b, hb, hxb, hmin⟩ := hlower
    obtain ⟨i, hi, he⟩ := exists_endpoint P y b ((hmem b).mp hb)
    have hxe : x < endpoint P i y := by rw [he]; exact hxb
    refine ⟨.inr (.inr (.inr (.inl i))), ?_⟩
    change y ∈ lowerBase R (P.domain i) (endpoint P i) ∧ x < endpoint P i y
    refine ⟨⟨hi, (mem_activeBase R (lowerRayCell (P.domain i) (endpoint P i)) y).mpr ?_⟩, hxe⟩
    refine ⟨⟨x, hx, hi, hxe⟩, ?_⟩
    intro t ht htB
    change y ∈ P.domain i ∧ t < endpoint P i y at ht
    have hbt := hmin t ((hmem t).mpr htB)
    have htb : t < b := by simpa only [he] using ht.2
    exact not_lt_of_ge hbt htb
  · obtain ⟨a, ha, hax, hmax⟩ := hupper
    obtain ⟨i, hi, he⟩ := exists_endpoint P y a ((hmem a).mp ha)
    have hex : endpoint P i y < x := by rw [he]; exact hax
    refine ⟨.inr (.inr (.inl i)), ?_⟩
    change y ∈ upperBase R (P.domain i) (endpoint P i) ∧ endpoint P i y < x
    refine ⟨⟨hi, (mem_activeBase R (upperRayCell (P.domain i) (endpoint P i)) y).mpr ?_⟩, hex⟩
    refine ⟨⟨x, hx, hi, hex⟩, ?_⟩
    intro t ht htB
    change y ∈ P.domain i ∧ endpoint P i y < t at ht
    have hta := hmax t ((hmem t).mpr htB)
    have hat : a < t := by simpa only [he] using ht.2
    exact not_lt_of_ge hta hat
  · obtain ⟨a, ha, b, hb, hax, hxb, hadj⟩ := hband
    obtain ⟨i, hi, hei⟩ := exists_endpoint P y a ((hmem a).mp ha)
    obtain ⟨j, hj, hej⟩ := exists_endpoint P y b ((hmem b).mp hb)
    have hix : endpoint P i y < x := by rw [hei]; exact hax
    have hxj : x < endpoint P j y := by rw [hej]; exact hxb
    refine ⟨.inr (.inl (i, j)), ?_⟩
    change y ∈ bandBase R (P.domain i ∩ P.domain j) (endpoint P i) (endpoint P j) ∧
      endpoint P i y < x ∧ x < endpoint P j y
    refine ⟨⟨⟨⟨hi, hj⟩, hix.trans hxj⟩,
      (mem_activeBase R (bandCell (P.domain i ∩ P.domain j) (endpoint P i) (endpoint P j)) y).mpr ?_⟩, hix, hxj⟩
    refine ⟨⟨x, hx, ⟨hi, hj⟩, hix, hxj⟩, ?_⟩
    intro t ht htB
    change y ∈ P.domain i ∩ P.domain j ∧ endpoint P i y < t ∧ t < endpoint P j y at ht
    have hat : a < t := by simpa only [hei] using ht.2.1
    have htb : t < b := by simpa only [hej] using ht.2.2
    rcases hadj t ((hmem t).mpr htB) with hta | hbt
    · exact not_lt_of_ge hta hat
    · exact not_lt_of_ge hbt htb

theorem cover (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (z : Fin (n + 1) → Values.Gamma (M := M))
    (hz : z ∈ R) : ∃ label : Label P.size, z ∈ stack R P label := by
  have he : Fin.cons (z 0) (Fin.tail z) = z := Fin.cons_self_tail z
  obtain ⟨label, hl⟩ := cover_cons R P (Fin.tail z) (z 0) (he.symm ▸ hz)
  exact ⟨label, he ▸ hl⟩

theorem union_stacks (h00 : M ⊨ Axioms.ACVF00) (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hR : GammaDefinable B R) (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) :
    R = ⋃ label : Label P.size, stack R P label := by
  ext z
  constructor
  · intro hz
    exact Set.mem_iUnion.mpr (cover R P z hz)
  · intro hz
    obtain ⟨label, hl⟩ := Set.mem_iUnion.mp hz
    exact stack_subset h00 R hR P label hl

end DiamondIntegral.Section4.GammaBoundaryStackCoverage
