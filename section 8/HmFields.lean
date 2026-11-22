import «section 8».HmIso
import «section 8».RESPieces
import FubiniTheorems.Prerequisites.Euler.RVNamedTuples
import FubiniTheorems.Prerequisites.Euler.RVTaggedCoproduct
import FubiniTheorems.Prerequisites.Euler.RVMeasuredProductProperties

/-! `h_m` on disjoint unions, one-point charts, the unit chart and grade casts.

* `hmValue_union`: additive on disjoint unions of charts with the same arity;
* `hmValue_tuple`: `1` on a one-point chart whose coordinates have lattice values (the tags and
  zero paddings of the tagged coproduct);
* `hmValue_unit`: `1` on the unit chart;
* `hmValue_castGrade`: unchanged by a cast of the grade. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal DiamondIntegral.Section8.PuiseuxValues
open DiamondIntegral.Section8.RESPieces RVChartDisjointUnion RVNamedTuples

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-! ### Disjoint unions -/

section union

variable {n k : ℕ} (a b : Data (base P) n k) (hd : Disjoint a.domain b.domain)

theorem latticeFibre_union (m : ℕ) (w : Γ) :
    latticeFibre P (disjointUnion a b hd).toChart m w =
      latticeFibre P a.toChart m w ∪ latticeFibre P b.toChart m w := by
  ext u
  constructor
  · rintro ⟨⟨hu, hl⟩, hw⟩
    rcases hu with hu | hu
    · exact Or.inl ⟨⟨hu, hl⟩, by rw [← disjointUnion_weight_left a b hd u hu]; exact hw⟩
    · exact Or.inr ⟨⟨hu, hl⟩, by rw [← disjointUnion_weight_right a b hd u hu]; exact hw⟩
  · rintro (⟨⟨hu, hl⟩, hw⟩ | ⟨⟨hu, hl⟩, hw⟩)
    · exact ⟨⟨Or.inl hu, hl⟩, by rw [disjointUnion_weight_left a b hd u hu]; exact hw⟩
    · exact ⟨⟨Or.inr hu, hl⟩, by rw [disjointUnion_weight_right a b hd u hu]; exact hw⟩

/-- **`h_m` is additive on disjoint unions.** -/
theorem hmValue_union (hu : RVMeasuredBounds.DomainBounded (disjointUnion a b hd).toChart)
    (ha : RVMeasuredBounds.DomainBounded a.toChart) (hb : RVMeasuredBounds.DomainBounded b.toChart)
    (m : ℕ+) :
    hmValue P (disjointUnion a b hd).toChart hu m = hmValue P a.toChart ha m + hmValue P b.toChart hb m := by
  have hterm : ∀ w, hmTerm P _ hu m w = hmTerm P _ ha m w + hmTerm P _ hb m w := by
    intro w
    have hdom : (fibreChart P _ hu m w).domain =
        latticeFibre P a.toChart m w ∪ latticeFibre P b.toChart m w :=
      (fibreChart_domain P _ hu m w).trans (latticeFibre_union P a b hd m w)
    have hcls : nativeRESChartClass (fibreChart P _ hu m w) =
        nativeRESChartClass (fibreChart P _ ha m w) + nativeRESChartClass (fibreChart P _ hb m w) := by
      rw [← classOn_domain (fibreChart P _ hu m w), hdom,
        classOn_union _ _ _ (latticeFibre_definable' P _ ha m w) (latticeFibre_definable' P _ hb m w)
          (fun u h => hdom ▸ Or.inl h) (fun u h => hdom ▸ Or.inr h)
          (Set.disjoint_of_subset (fun _ h => h.1.1) (fun _ h => h.1.1) hd),
        classOn_eq_of_domain (fibreChart P _ hu m w) _ (latticeFibre_definable' P _ ha m w) (fun u h => hdom ▸ Or.inl h)
          (fibreChart P _ ha m w) rfl (fun u => by simp only [Fin.cast_refl, Function.comp_id]; rfl),
        classOn_eq_of_domain (fibreChart P _ hu m w) _ (latticeFibre_definable' P _ hb m w) (fun u h => hdom ▸ Or.inr h)
          (fibreChart P _ hb m w) rfl (fun u => by simp only [Fin.cast_refl, Function.comp_id]; rfl)]
    simp only [hmTerm, hcls, map_add, AddMonoidAlgebra.single_add]
  have hS : weights P _ hu m ⊆ weights P _ ha m ∪ weights P _ hb m := by
    intro w hw
    rw [mem_weights] at hw
    obtain ⟨u, hu'⟩ := hw
    rw [latticeFibre_union] at hu'
    rcases hu' with h | h
    · exact Finset.mem_union_left _ ((mem_weights P _ ha m w).mpr ⟨u, h⟩)
    · exact Finset.mem_union_right _ ((mem_weights P _ hb m w).mpr ⟨u, h⟩)
  rw [hmValue_eq_sum P _ hu m _ hS, hmValue_eq_sum P _ ha m _ Finset.subset_union_left,
    hmValue_eq_sum P _ hb m _ Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => hterm w

end union

/-! ### One-point charts and the unit -/

theorem nativeRESChartClass_unit : nativeRESChartClass (RESChartRing.unit (base P)) = 1 := by
  change RESDimensionFreeReduction.fromOrdinary (base P)
    (RESOrdinaryRing.objectClass (RESChartRing.unit (base P))) = 1
  rw [RESOrdinaryRing.objectClass_unit, map_one]

theorem hmTerm_one_of_class {k : ℕ} (a : Chart (base P) k) (ha : RVMeasuredBounds.DomainBounded a)
    (m : ℕ+) (h : nativeRESChartClass (fibreChart P a ha m 1) = 1) : hmTerm P a ha m 1 = 1 := by
  rw [hmTerm, h, map_one, ratValue_one (one_lt_uniformizerValue P), mul_zero]
  rfl

/-- `h_m` is `1` on a one-point chart whose coordinates have lattice values. -/
theorem hmValue_tuple {nn : ℕ} (x : Fin nn → P.N) (hx : ∀ i, DefinableClosureAtBase (base P) .rv (x i))
    (h : RVMeasuredBounds.DomainBounded (tupleChart (base P) x hx)) (m : ℕ+)
    (hl : ∀ i, InLattice π m (codeValue (x i))) :
    hmValue P (tupleChart (base P) x hx) h m = 1 := by
  have hweight : ∀ u, (tupleChart (base P) x hx).correctedWeight u = 1 := fun u => by
    change 1 * (∏ i : Fin 0, codeValue (Fin.elim0 i)) = 1
    simp
  have hfib : latticeFibre P (tupleChart (base P) x hx) m 1 = {x} := by
    ext u
    constructor
    · rintro ⟨⟨hu, -⟩, -⟩; exact hu
    · intro hu
      have hux : u = x := hu
      rw [hux]
      exact ⟨⟨rfl, hl⟩, hweight x⟩
  have hsub : weights P _ h m ⊆ {1} := by
    intro w hw
    obtain ⟨u, -, hu⟩ := (mem_weights P _ h m w).mp hw
    rw [← hu, hweight]
    exact Finset.mem_singleton_self 1
  rw [hmValue_eq_sum P _ h m {1} hsub, Finset.sum_singleton]
  refine hmTerm_one_of_class P _ h m ?_
  rw [← nativeRESChartClass_unit P]
  refine nativeRESChartClass_iso _ _ (RVUnderlyingIsomorphisms.ofMap _ _ (fun u => u ∘ (Fin.elim0 : Fin 0 → Fin nn))
    (RVCoordinateMaps.coordinate_graph_definable (base P) _ (latticeFibre_definable' P _ h m 1) Fin.elim0)
    ⟨fun _ _ => Set.mem_univ _, fun u hu v hv _ => ?_, fun y _ => ⟨x, ?_, ?_⟩⟩)
  · have hu' : u ∈ latticeFibre P (tupleChart (base P) x hx) m 1 := hu
    have hv' : v ∈ latticeFibre P (tupleChart (base P) x hx) m 1 := hv
    rw [hfib] at hu' hv'
    exact hu'.trans hv'.symm
  · show x ∈ latticeFibre P (tupleChart (base P) x hx) m 1
    rw [hfib]; rfl
  · funext i
    exact Fin.elim0 (show Fin 0 from i)

/-- `h_m` is `1` on the unit chart. -/
theorem hmValue_unit (h : RVMeasuredBounds.DomainBounded (RVChartRing.unit (base P))) (m : ℕ+) :
    hmValue P (RVChartRing.unit (base P)) h m = 1 := by
  have hweight : ∀ u, (RVChartRing.unit (base P)).correctedWeight u = 1 := fun u =>
    weightedUnit_correctedWeight _ _ _ u
  have hfib : latticeFibre P (RVChartRing.unit (base P)) m 1 = Set.univ := by
    ext u
    exact ⟨fun _ => Set.mem_univ u, fun _ => ⟨⟨Set.mem_univ u, fun i => i.elim0⟩, hweight u⟩⟩
  have hsub : weights P _ h m ⊆ {1} := by
    intro w hw
    obtain ⟨u, -, hu⟩ := (mem_weights P _ h m w).mp hw
    rw [← hu, hweight]
    exact Finset.mem_singleton_self 1
  rw [hmValue_eq_sum P _ h m {1} hsub, Finset.sum_singleton]
  refine hmTerm_one_of_class P _ h m ?_
  rw [← nativeRESChartClass_unit P]
  refine class_eq_of_domain _ _ rfl fun u => ?_
  simp only [Fin.cast_refl, Function.comp_id]
  rw [fibreChart_domain, hfib]
  exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩

/-- `h_m` does not see a cast of the grade. -/
theorem hmValue_castGrade {nn k l : ℕ} (h : k = l) (a : Data (base P) nn k)
    (ha : RVMeasuredBounds.DomainBounded (castGrade h a).toChart)
    (ha' : RVMeasuredBounds.DomainBounded a.toChart) (m : ℕ+) :
    hmValue P (castGrade h a).toChart ha m = hmValue P a.toChart ha' m := by
  subst h
  rfl

end DiamondIntegral.Section8.Hm
