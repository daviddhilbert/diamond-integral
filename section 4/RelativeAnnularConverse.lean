import «section 4».RelativeAnnularGenerators

/-! Notation 4.17: the implemented generators of `J_var` are manuscript
generators, so the implemented ideal equals the manuscript ideal.

For an implemented presentation `P` (base `W`, aperture `τ`, source and
endpoint data with weights `ω_W` and `ω_W · τ`), the manuscript datum is
`U = W × (1)` with `j` the unit coordinate and the aperture `τ` read on `W`.
Its source, endpoint and shell are isomorphic to those of `P`, by one
coordinate reindexing that drops the unit coordinate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.RelativeAnnularConverse
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section4.AnnularBlowup DiamondIntegral.Section4.BlowupChart
open DiamondIntegral.Section4.BlowupRelation DiamondIntegral.Section4.RelativeAnnularGenerators

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

theorem head_ne_tail (n m : ℕ) (i : Fin m) (l : Fin n) : headIndex n m i ≠ tailIndex n m l := by
  intro h
  have := congrArg (join n m (fun _ => (0 : ℕ)) (fun _ => 1)) h
  simp only [join_head, join_tail] at this
  exact absurd this (by decide)

variable (P : FunctionalApertureCompatibility.Presentation B k)

/-- `U = W × (1)`. -/
def unitChart : Chart B (1 + k) := RVMeasuredProduct.product P.base.toChart unitPoint

/-- The unit coordinate. -/
def unitIdx : Fin (1 + k) := tailIndex 1 k 0

/-- The structural unit code. -/
abbrev one : M := GammaParameters.raw RVRadiusGenerators.oneCode

theorem mem_unitChart {u : Fin (1 + P.base.arity) → M} (hu : u ∈ (unitChart P).domain) :
    u ∘ headIndex 1 P.base.arity ∈ P.base.domain ∧ u ∘ tailIndex 1 P.base.arity = ![one] :=
  ⟨hu.1, hu.2⟩

theorem unitChart_reconstruct {u : Fin (1 + P.base.arity) → M} (hu : u ∈ (unitChart P).domain) :
    u = join 1 P.base.arity (u ∘ headIndex 1 P.base.arity) ![one] := by
  have h := join_reconstruct 1 P.base.arity u
  rw [(mem_unitChart P hu).2] at h
  exact h.symm

theorem join_mem_unitChart {x : Fin P.base.arity → M} (hx : x ∈ P.base.domain) :
    join 1 P.base.arity x ![one] ∈ (unitChart P).domain :=
  (RVRealProducts.productSet_join _ _ x ![one]).mpr ⟨hx, rfl⟩

theorem unitChart_weight {u : Fin (1 + P.base.arity) → M} (hu : u ∈ (unitChart P).domain) :
    (unitChart P).correctedWeight u = P.base.toChart.correctedWeight (u ∘ headIndex 1 P.base.arity) := by
  unfold unitChart
  rw [RVPointProductIsomorphisms.product_weight_coordinates]
  have h1 := RVPointChoices.pointChart_weight B RVRadiusGenerators.oneCode
    (RVRadiusGenerators.oneCode_definable B) ⟨u ∘ tailIndex 1 P.base.arity, hu.2⟩
  change P.base.toChart.correctedWeight (u ∘ headIndex 1 P.base.arity) *
      unitPoint.correctedWeight (u ∘ tailIndex 1 P.base.arity) = _
  rw [show unitPoint.correctedWeight (u ∘ tailIndex 1 P.base.arity) = 1 from
    h1.trans RVRadiusGenerators.oneCode_value, mul_one]

theorem unitChart_coordinate_head (u : Fin (1 + P.base.arity) → M) (i : Fin k) :
    (unitChart P).coordinate u (headIndex 1 k i) = P.base.coordinate (u ∘ headIndex 1 P.base.arity) i := by
  change join 1 k (P.base.coordinate (u ∘ headIndex 1 P.base.arity))
    (unitPoint.coordinate (u ∘ tailIndex 1 P.base.arity)) (headIndex 1 k i) = _
  rw [join_head]

theorem unitChart_finite : InactiveFinite (unitChart P) (unitIdx (k := k)) := by
  intro t
  apply ((P.base.finite_fibres (t ∘ headIndex 1 k)).image
    (fun x => join 1 P.base.arity x ![one])).subset
  rintro u ⟨hu, ht⟩
  refine ⟨u ∘ headIndex 1 P.base.arity, ⟨(mem_unitChart P hu).1, funext (fun i => ?_)⟩,
    (unitChart_reconstruct P hu).symm⟩
  have h := congrFun ht (headIndex 1 k i)
  simp only [inactive] at h
  rw [Function.update_of_ne (show headIndex 1 k i ≠ unitIdx from head_ne_tail 1 k i 0)] at h
  exact (unitChart_coordinate_head P u i).symm.trans h

/-- The aperture `τ` read on `W`. -/
def unitAperture : Aperture (unitChart P) where
  aperture u := P.aperture (u ∘ headIndex 1 P.base.arity)
  graph_definable := RVGraphComposition.graph_compose_definable B (unitChart P).domain P.base.domain
    (fun u => u ∘ headIndex 1 P.base.arity) (fun x => ![P.aperture x])
    (RVCoordinateMaps.coordinate_graph_definable B _ (unitChart P).domain_definable (headIndex 1 P.base.arity))
    P.graph_definable (fun _ hu => hu.1)
  nonzero _ hu := P.aperture_nonzero _ hu.1
  nonnegative _ hu := P.aperture_nonnegative _ hu.1
  bound := P.upperBound
  bounded _ hu := P.aperture_bounded _ hu.1

theorem unitChart_bounded : RVMeasuredBounds.DomainBounded (unitChart P) :=
  (RVBoundedCharts.product P.base
    (RVRadiusIdeal.boundedPoint B RVRadiusGenerators.oneCode (RVRadiusGenerators.oneCode_definable B))).domain_bounded

/-- The manuscript datum of an implemented presentation. -/
def datum : AnnularDatum B k where
  chart := unitChart P
  coordinate := unitIdx
  finite := unitChart_finite P
  aperture := unitAperture P
  bounded := unitChart_bounded P

/-- Dropping the unit coordinate from a graph point of `U`. -/
def dropUnit (n : ℕ) : Fin (1 + n) → Fin (1 + (1 + n)) :=
  join 1 n (fun i => headIndex 1 (1 + n) (headIndex 1 n i)) ![tailIndex 1 (1 + n) 0]

omit [LRV.Structure M] hM in
theorem dropUnit_head (n : ℕ) (w : Fin (1 + (1 + n)) → M) :
    (w ∘ dropUnit n) ∘ headIndex 1 n = (w ∘ headIndex 1 (1 + n)) ∘ headIndex 1 n := by
  funext i
  simp only [Function.comp_apply, dropUnit, join_head]

omit [LRV.Structure M] hM in
theorem dropUnit_tail (n : ℕ) (w : Fin (1 + (1 + n)) → M) :
    (w ∘ dropUnit n) ∘ tailIndex 1 n = w ∘ tailIndex 1 (1 + n) := by
  funext i
  fin_cases i
  simp only [Function.comp_apply, dropUnit, join_tail]
  rfl

/-- The canonical graph point of `U` over a point of `W`. -/
def liftPoint (x : Fin (1 + P.base.arity) → M) : Fin (1 + (1 + P.base.arity)) → M :=
  join 1 (1 + P.base.arity) (join 1 P.base.arity (x ∘ headIndex 1 P.base.arity) ![one])
    (x ∘ tailIndex 1 P.base.arity)

theorem liftPoint_drop (x : Fin (1 + P.base.arity) → M) : liftPoint P x ∘ dropUnit P.base.arity = x := by
  have h1 : (liftPoint P x ∘ headIndex 1 (1 + P.base.arity)) ∘ headIndex 1 P.base.arity =
      x ∘ headIndex 1 P.base.arity := by
    funext i
    simp only [Function.comp_apply, liftPoint, join_head]
  have h2 : liftPoint P x ∘ tailIndex 1 (1 + P.base.arity) = x ∘ tailIndex 1 P.base.arity :=
    funext (join_tail 1 (1 + P.base.arity) _ _)
  rw [← join_reconstruct 1 P.base.arity (liftPoint P x ∘ dropUnit P.base.arity), dropUnit_head,
    dropUnit_tail, h1, h2, join_reconstruct]

/-- The graph domain of `U` corresponds to the graph domain over `W`. -/
theorem graph_bij {D : Set (Fin P.base.arity → M)} (hD : D = P.base.domain) :
    Set.BijOn (fun w => w ∘ dropUnit P.base.arity)
      (graphOn (unitChart P).domain (fun u => ![(unitAperture P).aperture u]))
      (graphOn D (fun x => ![P.aperture x])) := by
  have key : ∀ w ∈ graphOn (unitChart P).domain (fun u => ![(unitAperture P).aperture u]),
      w = liftPoint P (w ∘ dropUnit P.base.arity) := by
    intro w hw
    have h1 := join_reconstruct 1 (1 + P.base.arity) w
    have h2 : w ∘ headIndex 1 (1 + P.base.arity) =
        join 1 P.base.arity ((w ∘ headIndex 1 (1 + P.base.arity)) ∘ headIndex 1 P.base.arity) ![one] :=
      unitChart_reconstruct P hw.1
    unfold liftPoint
    rw [dropUnit_head, dropUnit_tail, ← h2]
    exact h1.symm
  refine ⟨fun w hw => ?_, fun w hw v hv he => ?_, fun x hx => ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [dropUnit_head, hD]
      exact (mem_unitChart P hw.1).1
    · rw [dropUnit_head, dropUnit_tail]
      exact hw.2
  · rw [key w hw, key v hv]
    exact congrArg (liftPoint P) he
  · refine ⟨liftPoint P x, ⟨?_, ?_⟩, liftPoint_drop P x⟩
    · have hh : liftPoint P x ∘ headIndex 1 (1 + P.base.arity) =
          join 1 P.base.arity (x ∘ headIndex 1 P.base.arity) ![one] :=
        funext (join_head 1 (1 + P.base.arity) _ _)
      rw [hh]
      exact join_mem_unitChart P (hD ▸ hx.1)
    · have hh : liftPoint P x ∘ headIndex 1 (1 + P.base.arity) =
          join 1 P.base.arity (x ∘ headIndex 1 P.base.arity) ![one] :=
        funext (join_head 1 (1 + P.base.arity) _ _)
      have ht : liftPoint P x ∘ tailIndex 1 (1 + P.base.arity) = x ∘ tailIndex 1 P.base.arity :=
        funext (join_tail 1 (1 + P.base.arity) _ _)
      rw [hh, ht]
      change ![P.aperture ((join 1 P.base.arity (x ∘ headIndex 1 P.base.arity) ![one]) ∘
        headIndex 1 P.base.arity)] = _
      rw [show (join 1 P.base.arity (x ∘ headIndex 1 P.base.arity) ![one]) ∘ headIndex 1 P.base.arity =
        x ∘ headIndex 1 P.base.arity from funext (join_head 1 P.base.arity _ _)]
      exact hx.2

theorem annular_mem_iff {k' : ℕ} (r : Chart B k') (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (w : Fin (1 + r.arity) → M) :
    w ∈ (VariableApertureRayCancellation.annularChart r j).domain ↔
      w ∘ headIndex 1 r.arity ∈ r.domain ∧ Proper (w ∘ tailIndex 1 r.arity) ∧
        1 < codeValue (w (tailIndex 1 r.arity 0)) ∧
        codeValue (w (tailIndex 1 r.arity 0)) ≤ codeValue ((w ∘ headIndex 1 r.arity) j) := by
  have h := VariableApertureRayCancellation.annularChart_join_iff r j hp (w ∘ headIndex 1 r.arity)
    (w ∘ tailIndex 1 r.arity)
  rw [join_reconstruct] at h
  exact h

theorem annular_weight {k' : ℕ} (r : Chart B k') (j : Fin r.arity) (w : Fin (1 + r.arity) → M) :
    (VariableApertureRayCancellation.annularChart r j).correctedWeight w =
      r.correctedWeight (w ∘ headIndex 1 r.arity) * codeValue (w (tailIndex 1 r.arity 0)) := by
  change (RVMeasuredProduct.product r
    (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))).correctedWeight w = _
  rw [RVPointProductIsomorphisms.product_weight_coordinates, VariableApertureMeasuredComparison.ray_weight]
  rfl

/-- The Section 4 presentation of the datum of `P`. -/
abbrev Q : FunctionalApertureCompatibility.Presentation B k :=
  presentation (unitChart P) unitIdx (unitChart_finite P) (unitAperture P) (unitChart_bounded P)

def sourceIso' : Iso (Q P).toCoordinate.sourceBounded.toChart P.toCoordinate.sourceBounded.toChart :=
  RVCoordinateMaps.coordinateIso _ _ (dropUnit P.base.arity) (graph_bij P P.source_domain) (by
    intro w hw
    have hm : (w ∘ dropUnit P.base.arity) ∘ headIndex 1 P.base.arity ∈ P.base.domain :=
      (dropUnit_head P.base.arity w).symm ▸ (mem_unitChart P hw.1).1
    exact (unitChart_weight P hw.1).trans ((congrArg P.base.toChart.correctedWeight
      (dropUnit_head P.base.arity w).symm).trans (P.source_weight _ hm).symm))

def endpointIso' : Iso (Q P).toCoordinate.endpointBounded.toChart P.toCoordinate.endpointBounded.toChart :=
  RVCoordinateMaps.coordinateIso _ _ (dropUnit P.base.arity) (graph_bij P P.endpoint_domain) (by
    intro w hw
    have hm : (w ∘ dropUnit P.base.arity) ∘ headIndex 1 P.base.arity ∈ P.base.domain :=
      (dropUnit_head P.base.arity w).symm ▸ (mem_unitChart P hw.1).1
    have e1 := endpointBase_weight (unitChart P) unitIdx (unitChart_finite P) (unitAperture P) _ hw.1
    have e2 := (baseChart_weight (unitChart P) unitIdx (unitChart_finite P) _).trans (unitChart_weight P hw.1)
    exact e1.trans ((congrArg (· * codeValue ((unitAperture P).aperture _)) e2).trans
      ((congrArg (fun z => P.base.toChart.correctedWeight z * codeValue (P.aperture z))
        (dropUnit_head P.base.arity w).symm).trans (P.endpoint_weight _ hm).symm)))

/-- Dropping the unit coordinate from a shell point. -/
def dropShell (n : ℕ) : Fin (1 + (1 + n)) → Fin (1 + (1 + (1 + n))) :=
  join 1 (1 + n) (fun i => headIndex 1 (1 + (1 + n)) (dropUnit n i)) ![tailIndex 1 (1 + (1 + n)) 0]

omit [LRV.Structure M] hM in
theorem dropShell_head (n : ℕ) (w : Fin (1 + (1 + (1 + n))) → M) :
    (w ∘ dropShell n) ∘ headIndex 1 (1 + n) = (w ∘ headIndex 1 (1 + (1 + n))) ∘ dropUnit n := by
  funext i
  simp only [Function.comp_apply, dropShell, join_head]

omit [LRV.Structure M] hM in
theorem dropShell_tail (n : ℕ) (w : Fin (1 + (1 + (1 + n))) → M) :
    (w ∘ dropShell n) ∘ tailIndex 1 (1 + n) = w ∘ tailIndex 1 (1 + (1 + n)) := by
  funext i
  fin_cases i
  simp only [Function.comp_apply, dropShell, join_tail]
  rfl

omit [LRV.Structure M] hM in
theorem dropUnit_aperture (n : ℕ) (w : Fin (1 + (1 + n)) → M) :
    (w ∘ dropUnit n) (tailIndex 1 n 0) = w (tailIndex 1 (1 + n) 0) := by
  simp only [Function.comp_apply, dropUnit, join_tail]
  rfl

theorem Qgraph_nonzero : ∀ x ∈ (Q P).graphChart.domain,
    NonzeroRV (x (tailIndex 1 (Q P).base.arity 0)) := by
  intro x hx
  have h := congrFun hx.2 0
  change P.aperture ((x ∘ headIndex 1 (1 + P.base.arity)) ∘ headIndex 1 P.base.arity) =
    x (tailIndex 1 (1 + P.base.arity) 0) at h
  exact h ▸ P.aperture_nonzero _ (mem_unitChart P hx.1).1

theorem Pgraph_nonzero : ∀ x ∈ P.graphChart.domain, NonzeroRV (x (tailIndex 1 P.base.arity 0)) := by
  intro x hx
  have h := congrFun hx.2 0
  change P.aperture (x ∘ headIndex 1 P.base.arity) = x (tailIndex 1 P.base.arity 0) at h
  exact h ▸ P.aperture_nonzero _ hx.1

set_option maxHeartbeats 2000000 in
def shellIso' : Iso (Q P).toCoordinate.shell.toChart P.toCoordinate.shell.toChart := by
  refine RVCoordinateMaps.coordinateIso _ _ (dropShell P.base.arity) ?_ ?_
  · have hg := graph_bij P (D := P.base.domain) rfl
    have hQ := annular_mem_iff (Q P).graphChart (tailIndex 1 (Q P).base.arity 0) (Qgraph_nonzero P)
    have hP := annular_mem_iff P.graphChart (tailIndex 1 P.base.arity 0) (Pgraph_nonzero P)
    refine ⟨fun w hw => ?_, fun w hw v hv he => ?_, fun y hy => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := (hQ w).mp hw
      refine (hP _).mpr ⟨?_, ?_, ?_, ?_⟩
      · show (w ∘ dropShell P.base.arity) ∘ headIndex 1 (1 + P.base.arity) ∈ P.graphChart.domain
        rw [dropShell_head]
        exact hg.1 h1
      · show Proper ((w ∘ dropShell P.base.arity) ∘ tailIndex 1 (1 + P.base.arity))
        rw [dropShell_tail]
        exact h2
      · show 1 < codeValue (((w ∘ dropShell P.base.arity) ∘ tailIndex 1 (1 + P.base.arity)) 0)
        rw [dropShell_tail]
        exact h3
      · show codeValue (((w ∘ dropShell P.base.arity) ∘ tailIndex 1 (1 + P.base.arity)) 0) ≤
          codeValue (((w ∘ dropShell P.base.arity) ∘ headIndex 1 (1 + P.base.arity)) (tailIndex 1 P.base.arity 0))
        rw [dropShell_tail, dropShell_head, dropUnit_aperture]
        exact h4
    · have hw' := (hQ w).mp hw
      have hv' := (hQ v).mp hv
      have he' : w ∘ dropShell P.base.arity = v ∘ dropShell P.base.arity := he
      have eh := congrArg (fun z => z ∘ headIndex 1 (1 + P.base.arity)) he'
      have et := congrArg (fun z => z ∘ tailIndex 1 (1 + P.base.arity)) he'
      rw [dropShell_head, dropShell_head] at eh
      rw [dropShell_tail, dropShell_tail] at et
      have hh : w ∘ headIndex 1 (1 + (1 + P.base.arity)) = v ∘ headIndex 1 (1 + (1 + P.base.arity)) :=
        hg.2.1 hw'.1 hv'.1 eh
      rw [← join_reconstruct 1 (1 + (1 + P.base.arity)) w, ← join_reconstruct 1 (1 + (1 + P.base.arity)) v,
        hh, et]
    · obtain ⟨h1, h2, h3, h4⟩ := (hP y).mp hy
      obtain ⟨x, hx, hxy⟩ := hg.2.2 h1
      have hxy' : x ∘ dropUnit P.base.arity = y ∘ headIndex 1 (1 + P.base.arity) := hxy
      let w := join 1 (1 + (1 + P.base.arity)) x (y ∘ tailIndex 1 (1 + P.base.arity))
      have hwh : w ∘ headIndex 1 (1 + (1 + P.base.arity)) = x := funext (join_head 1 _ _ _)
      have hwt : w ∘ tailIndex 1 (1 + (1 + P.base.arity)) = y ∘ tailIndex 1 (1 + P.base.arity) :=
        funext (join_tail 1 _ _ _)
      refine ⟨w, (hQ w).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · show w ∘ headIndex 1 (1 + (1 + P.base.arity)) ∈ (Q P).graphChart.domain
        rw [hwh]
        exact hx
      · show Proper (w ∘ tailIndex 1 (1 + (1 + P.base.arity)))
        rw [hwt]
        exact h2
      · show 1 < codeValue ((w ∘ tailIndex 1 (1 + (1 + P.base.arity))) 0)
        rw [hwt]
        exact h3
      · show codeValue ((w ∘ tailIndex 1 (1 + (1 + P.base.arity))) 0) ≤
          codeValue ((w ∘ headIndex 1 (1 + (1 + P.base.arity))) (tailIndex 1 (1 + P.base.arity) 0))
        rw [hwt, hwh, ← dropUnit_aperture P.base.arity x, hxy']
        exact h4
      · show w ∘ dropShell P.base.arity = y
        conv_rhs => rw [← join_reconstruct 1 (1 + P.base.arity) y]
        conv_lhs => rw [← join_reconstruct 1 (1 + P.base.arity) (w ∘ dropShell P.base.arity)]
        rw [dropShell_head, dropShell_tail, hwh, hwt, hxy']
  · intro w hw
    have h1 := ((annular_mem_iff (Q P).graphChart (tailIndex 1 (Q P).base.arity 0) (Qgraph_nonzero P)) w).mp hw
    have A := (baseChart_weight (unitChart P) unitIdx (unitChart_finite P)
        ((w ∘ headIndex 1 (1 + (1 + P.base.arity))) ∘ headIndex 1 (1 + P.base.arity))).trans
      ((unitChart_weight P h1.1.1).trans (congrArg P.base.toChart.correctedWeight
        ((congrArg (fun z => z ∘ headIndex 1 P.base.arity) (dropShell_head P.base.arity w)).trans
          (dropUnit_head P.base.arity (w ∘ headIndex 1 (1 + (1 + P.base.arity))))).symm))
    have Bq := congrArg codeValue (congrFun (dropShell_tail P.base.arity w) 0).symm
    exact (annular_weight (Q P).graphChart (tailIndex 1 (Q P).base.arity 0) w).trans
      ((congrArg₂ (· * ·) A Bq).trans
        (annular_weight P.graphChart (tailIndex 1 P.base.arity 0) (w ∘ dropShell P.base.arity)).symm)

/-- Every implemented generator is a manuscript generator. -/
theorem relation_eq_generator : P.relation = (datum P).generator := by
  rw [AnnularDatum.generator_eq_relation]
  change P.toCoordinate.relation = (Q P).toCoordinate.relation
  unfold VariableApertureCompatibility.Presentation.relation
  rw [RVBoundedRing.objectClass_iso (shellIso' P), RVBoundedRing.objectClass_iso (endpointIso' P),
    RVBoundedRing.objectClass_iso (sourceIso' P)]

/-- Notation 4.17: the implemented ideal is the manuscript ideal `J_var`. -/
theorem ideal_eq_manuscriptIdeal : FunctionalApertureCompatibility.ideal B = manuscriptIdeal B := by
  apply le_antisymm _ manuscriptIdeal_le
  apply Ideal.span_le.mpr
  rintro x ⟨k, P, rfl⟩
  rw [relation_eq_generator P]
  exact Ideal.subset_span ⟨k, datum P, rfl⟩

end DiamondIntegral.Section4.RelativeAnnularConverse
