import «section 4».RVChartCoordinateMap
import «section 4».RVCoordinatePieceCover
import «section 4».FieldGrowthFiltration
import «section 4».RVResidueIsomorphisms

/-! Actual degree-k RES objects have residue classes in the k-th growth
piece. Auxiliary residue normalizations do not alter the original base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESResidueGrowth
open RVResidueCodes RVResidueScaledCovers RVMeasuredCharts FieldGrowthFiltration
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def domain {S : Set M} {n k : ℕ}
    {A : Set (Fin n → CanonicalRV.RVSort M)} (C : Code A)
    (i : C.cover.Index) (D : RVCoordinatePiece (M := M) S n k) :
    Set (Fin C.chart.arity → ModelResidue M) :=
  {x | x ∈ C.chart.domain ∧ x ∈ (C.cover.piece i).guard ∧ C.decode x ∈ D.source.carrier}

theorem domain_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {n k : ℕ} {A : Set (Fin n → CanonicalRV.RVSort M)} (C : Code A)
    (i : C.cover.Index) (D : RVCoordinatePiece (M := M) S n k) : PureDef (domain C i D) := by
  have h := C.chart.definable.inter ((C.cover.piece i).definable.inter
    ((residue_pullback_pure hc D.source (C.cover.piece i).scale).preimage_comp
      (C.cover.piece i).coord))
  convert h using 1
  ext x
  change (x ∈ C.chart.domain ∧ x ∈ (C.cover.piece i).guard ∧ C.decode x ∈ D.source.carrier) ↔
    (x ∈ C.chart.domain ∧ x ∈ (C.cover.piece i).guard ∧ (C.cover.piece i).value x ∈ D.source.carrier)
  constructor <;> rintro ⟨hx, hi, hd⟩
  · exact ⟨hx, hi, (C.cover.agrees i x hx hi) ▸ hd⟩
  · exact ⟨hx, hi, (C.cover.agrees i x hx hi).symm ▸ hd⟩

theorem domain_good (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) {S : Set M} (hsmall : Cardinal.mk S < κ)
    {n k : ℕ} {A : Set (Fin n → CanonicalRV.RVSort M)} (C : Code A)
    (i : C.cover.Index) (D : RVCoordinatePiece (M := M) S n k) :
    Good k (⟨C.chart.arity, domain C i D, domain_definable hc C i D⟩ :
      FieldDefinableRing.Chart (ModelResidue M)) := by
  obtain ⟨N, hN⟩ := RVCoordinatePieceCover.uniform_bound hs hsmall D
  have hb := FieldBoundedProjection.of_fibre_ncard_le
    (fun y => (hN y).1) (fun y => (hN y).2)
  refine ⟨D.arity, D.bound, (C.cover.piece i).coord ∘ D.select, N, ?_⟩
  intro x hx he
  have hdecode (j : Fin (N + 1)) :
      C.decode (x j) = (C.cover.piece i).value (x j) :=
    C.cover.agrees i (x j) (hx j).1 (hx j).2.1
  have hproj (j : Fin (N + 1)) : C.decode (x j) ∘ D.select = C.decode (x 0) ∘ D.select := by
    rw [hdecode j, hdecode 0]
    funext a
    change (C.cover.piece i).scale (D.select a) * residueRV ((x j) ((C.cover.piece i).coord (D.select a))) =
      (C.cover.piece i).scale (D.select a) * residueRV ((x 0) ((C.cover.piece i).coord (D.select a)))
    exact congrArg (fun z => (C.cover.piece i).scale (D.select a) * residueRV z) (congrFun (he j) a)
  obtain ⟨j, l, hjl, hsame⟩ := hb (fun j => C.decode (x j)) (fun j => (hx j).2.2) hproj
  exact ⟨j, l, hjl, C.bijective.injOn (hx j).1 (hx l).1 hsame⟩

theorem value_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) [Infinite (ModelResidue M)] {κ : Cardinal}
    (hs : Saturated M κ) (B : Base (M := M)) (hsmall : Cardinal.mk (commonRealNames B) < κ)
    {k : ℕ} (a : RESChart B k) : RVResidueIsomorphisms.value hc a ∈ piece k := by
  let A := RVResidueChartCodes.typedSet a.toChart
  letI := RVResidueChartCodes.patterns_finite a
  let C := RVResidueCodes.code hc A
  obtain ⟨m, D, hD⟩ := RVCoordinatePieceCover.exists_cover hc hex hs hsmall A
    (RVChartCoordinateMap.dimension_le a.toChart)
  letI : Finite C.cover.Index := C.cover.finite
  let U (j : C.cover.Index × Fin m) := domain C j.1 (D j.2)
  have hU (j : C.cover.Index × Fin m) : PureDef (U j) := domain_definable hc C j.1 (D j.2)
  have hgood (j : C.cover.Index × Fin m) :
      Good k (⟨C.chart.arity, U j, hU j⟩ : FieldDefinableRing.Chart (ModelResidue M)) :=
    domain_good hc hs hsmall C j.1 (D j.2)
  have hset : (⋃ j, U j) = C.chart.domain := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hx⟩
      exact hx.1
    · intro hx
      obtain ⟨i, hi⟩ := C.cover.covers x hx
      obtain ⟨j, hj⟩ := hD (C.decode x) (C.bijective.mapsTo hx)
      exact ⟨(i, j), hx, hi, hj⟩
  have hm := finite_union_mem U hU hgood
  have heq : (⟨C.chart.arity, ⋃ j, U j, Set.definable_iUnion_of_finite hU⟩ :
      FieldDefinableRing.Chart (ModelResidue M)) = C.chart := by
    exact chart_eq hset _ _
  rw [heq] at hm
  exact hm

end DiamondIntegral.Section4.RESResidueGrowth
