import «section 4».RVStrictBoundedCompatibility

/-! Notation 4.17's `J_var` read on `∞`-free charts (Definition 4.9).

An admissible datum (`RelativeAnnularGenerators.AnnularDatum`) whose source has
no `∞` coordinate has shell and endpoint without `∞` coordinates as well
(`shell_infinityFree`, `endpoint_infinityFree`), so its generator
`[U^{τ,j}] - [U]` is an element `strictGenerator` of the strict ring.
`strictAnnularIdeal` is the ideal these strict generators span.

Every datum splits by the `∞`-pattern `p` of its source into data `stripDatum D p`
on the `∞`-free strips (the `∞` coordinates deleted, labels, forms and aperture
read through `unstrip`), and `generator_eq_sum_strip` shows
`D.generator = ∑ p, (stripDatum D p).generator` in the bounded ring. Hence
`map_strictAnnularIdeal`: the strict `J_var` maps exactly onto
`manuscriptIdeal B`, and `strictAnnularIdeal_eq` identifies it with the
transported ideal `strictManuscriptIdeal`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVStrictAnnularGenerators
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section4.AnnularBlowup DiamondIntegral.Section4.BlowupChart
open DiamondIntegral.Section4.BlowupRelation DiamondIntegral.Section4.RelativeAnnularGenerators
open DiamondIntegral.Section4.RVStrictBoundedComparison DiamondIntegral.Section4.RVChartDisjointUnion
open DiamondIntegral.Section4.RVChartRestrictions DiamondIntegral.Section4.RVMeasuredBounds
open DiamondIntegral.Section4.FiniteTupleGraphProduct

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### Index bookkeeping -/

omit [LRV.Structure M] hM in
theorem coordIndex_head {n : ℕ} (c : ℕ) (p : Finset (Fin n)) (i : Fin (stripArity p)) :
    coordIndex c p (headIndex c (stripArity p) i) = headIndex c n (stripIndex p i) :=
  join_head c (stripArity p) _ _ i

omit [LRV.Structure M] hM in
theorem coordIndex_tail {n : ℕ} (c : ℕ) (p : Finset (Fin n)) (l : Fin c) :
    coordIndex c p (tailIndex c (stripArity p) l) = tailIndex c n l :=
  join_tail c (stripArity p) _ _ l

/-- Delete the `p`-coordinates from a shell tuple. -/
def shellIndex {n : ℕ} (p : Finset (Fin n)) : Fin (1 + (1 + stripArity p)) → Fin (1 + (1 + n)) :=
  join 1 (1 + stripArity p) (fun i => headIndex 1 (1 + n) (coordIndex 1 p i)) (tailIndex 1 (1 + n))

omit [LRV.Structure M] hM in
theorem shellIndex_head {n : ℕ} (p : Finset (Fin n)) (i : Fin (1 + stripArity p)) :
    shellIndex p (headIndex 1 (1 + stripArity p) i) = headIndex 1 (1 + n) (coordIndex 1 p i) :=
  join_head 1 (1 + stripArity p) _ _ i

omit [LRV.Structure M] hM in
theorem shellIndex_tail {n : ℕ} (p : Finset (Fin n)) (l : Fin 1) :
    shellIndex p (tailIndex 1 (1 + stripArity p) l) = tailIndex 1 (1 + n) l :=
  join_tail 1 (1 + stripArity p) _ _ l

omit [LRV.Structure M] hM in
theorem join_shellIndex {n : ℕ} (p : Finset (Fin n)) (g : Fin (1 + n) → M) (z : Fin 1 → M) :
    join 1 (1 + n) g z ∘ shellIndex p = join 1 (1 + stripArity p) (g ∘ coordIndex 1 p) z := by
  apply block_ext 1 (1 + stripArity p)
  · funext i
    simp only [Function.comp_apply, shellIndex_head, join_head]
  · funext l
    simp only [Function.comp_apply, shellIndex_tail, join_tail]

/-! ### The strip datum -/

section Strip
variable (D : AnnularDatum B k) (p : Finset (Fin D.chart.arity))

/-- The `p`-strip of the source: the `∞`-coordinates of pattern `p` deleted. -/
abbrev stripChart : Chart B (1 + k) := (strip (ofChart D.chart) p).toChart

theorem stripChart_finite : InactiveFinite (stripChart D p) D.coordinate := by
  intro t
  apply ((D.finite t).image (fun u => u ∘ stripIndex p)).subset
  rintro v ⟨hv, hvt⟩
  obtain ⟨u, hu, _, hut, hun⟩ := stripDomain_cases hv
  refine ⟨u, ⟨hu, ?_⟩, hut⟩
  change Function.update (D.chart.coordinate (unstrip p v)) D.coordinate iRVOne = t at hvt
  rw [hun] at hvt
  exact hvt

/-- The aperture graph of the strip is the image of the `p`-part of the original graph. -/
theorem strip_graph_eq :
    (RVDefinableGraphExtension.domain (stripChart D p) (fun v => D.aperture.aperture (unstrip p v)) :
        Set (Fin (1 + stripArity p) → M)) =
      (fun w => w ∘ coordIndex 1 p) '' ((graphChart D.chart D.aperture).domain ∩
        {w | w ∘ headIndex 1 D.chart.arity ∈ patternSet p ∧
          w ∈ sortedUniverse (fun _ : Fin (1 + D.chart.arity) => SortTag.rv)}) := by
  ext v
  change (v ∘ headIndex 1 (stripArity p) ∈ stripDomain (ofChart D.chart) p ∧
      ![D.aperture.aperture (unstrip p (v ∘ headIndex 1 (stripArity p)))] = v ∘ tailIndex 1 (stripArity p)) ↔ _
  constructor
  · rintro ⟨hv, he⟩
    obtain ⟨u, hu, hup, hut, hun⟩ := stripDomain_cases hv
    let w := join 1 D.chart.arity u ![D.aperture.aperture u]
    have hwh : w ∘ headIndex 1 D.chart.arity = u := funext (join_head 1 D.chart.arity _ _)
    have hwt : w ∘ tailIndex 1 D.chart.arity = ![D.aperture.aperture u] := funext (join_tail 1 D.chart.arity _ _)
    have hg : w ∈ (graphChart D.chart D.aperture).domain := by
      refine ⟨?_, ?_⟩
      · rw [hwh]; exact hu
      · rw [hwh, hwt]
    refine ⟨w, ⟨hg, by rw [hwh]; exact hup, (graphChart D.chart D.aperture).domain_definable.proper w hg⟩, ?_⟩
    rw [hun] at he
    show join 1 D.chart.arity u ![D.aperture.aperture u] ∘ coordIndex 1 p = v
    rw [join_coordIndex, hut, he]
    exact join_reconstruct 1 (stripArity p) v
  · rintro ⟨w, ⟨hw, hp, _⟩, rfl⟩
    have key := (congrArg (fun x => x ∘ coordIndex 1 p) (graph_canonical D.chart D.aperture hw)).trans
      (join_coordIndex p _ _)
    beta_reduce
    rw [key]
    have hh := funext (join_head 1 (stripArity p) ((w ∘ headIndex 1 D.chart.arity) ∘ stripIndex p)
      ![D.aperture.aperture (w ∘ headIndex 1 D.chart.arity)])
    have ht := funext (join_tail 1 (stripArity p) ((w ∘ headIndex 1 D.chart.arity) ∘ stripIndex p)
      ![D.aperture.aperture (w ∘ headIndex 1 D.chart.arity)])
    change join 1 (stripArity p) _ _ ∘ headIndex 1 (stripArity p) = _ at hh
    change join 1 (stripArity p) _ _ ∘ tailIndex 1 (stripArity p) = _ at ht
    rw [hh, ht, unstrip_comp hp]
    exact ⟨⟨w ∘ headIndex 1 D.chart.arity, ⟨hw.1, hp⟩, rfl⟩, rfl⟩

/-- The aperture read on the strip. -/
def stripAperture : Aperture (stripChart D p) where
  aperture v := D.aperture.aperture (unstrip p v)
  graph_definable := by
    rw [strip_graph_eq]
    exact ((graphChart D.chart D.aperture).domain_definable.inter
      ((patternSet_definable B p).preimage_real (fun _ : Fin (1 + D.chart.arity) => SortTag.rv)
        (headIndex 1 D.chart.arity))).image_real (coordIndex 1 p)
  nonzero v hv := by
    obtain ⟨u, hu, _, _, hun⟩ := stripDomain_cases hv
    rw [hun]; exact D.aperture.nonzero u hu
  nonnegative v hv := by
    obtain ⟨u, hu, _, _, hun⟩ := stripDomain_cases hv
    rw [hun]; exact D.aperture.nonnegative u hu
  bound := D.aperture.bound
  bounded v hv := by
    obtain ⟨u, hu, _, _, hun⟩ := stripDomain_cases hv
    rw [hun]; exact D.aperture.bounded u hu

/-- The datum on the `p`-strip of the source. -/
def stripDatum : AnnularDatum B k where
  chart := stripChart D p
  coordinate := D.coordinate
  finite := stripChart_finite D p
  aperture := stripAperture D p
  bounded := strip_bounded (ofChart D.chart) D.bounded p

theorem stripDatum_infinityFree : InfinityFree (stripDatum D p).chart :=
  strip_infinityFree (ofChart D.chart) p

end Strip

/-! ### Strict generators -/

theorem graph_infinityFree (D : AnnularDatum B k) (h : InfinityFree D.chart) :
    ∀ w ∈ (graphChart D.chart D.aperture).domain, ∀ i, w i ≠ iRVZero := by
  intro w hw
  apply GammaBoundedProducts.all_coordinates 1 D.chart.arity (fun t => t ≠ iRVZero) w
  · intro i; exact h _ hw.1 i
  · intro l
    fin_cases l
    exact (graph_aperture_nonzero D.chart D.aperture w hw).2

theorem endpoint_infinityFree (D : AnnularDatum B k) (h : InfinityFree D.chart) :
    InfinityFree (endpointChart D.chart D.coordinate D.finite D.aperture) :=
  graph_infinityFree D h

theorem shell_infinityFree (D : AnnularDatum B k) (h : InfinityFree D.chart) :
    InfinityFree (shellChart D.chart D.coordinate D.finite D.aperture) := by
  intro w hw
  obtain ⟨hg, hz, _, _⟩ := shell_mem D.chart D.aperture hw
  apply GammaBoundedProducts.all_coordinates 1 (1 + D.chart.arity) (fun t => t ≠ iRVZero) w
  · intro i; exact graph_infinityFree D h _ hg i
  · intro l; exact (hz l).2

/-- Notation 4.17's generator `[U^{τ,j}] - [U]` of an `∞`-free datum, in the strict ring. -/
def strictGenerator (D : AnnularDatum B k) (h : InfinityFree D.chart) : StrictRing B :=
  objectClass (⟨shellBounded D.chart D.coordinate D.finite D.aperture D.bounded, shell_infinityFree D h⟩ :
      StrictChart B (1 + k)) +
    objectClass (⟨endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded, endpoint_infinityFree D h⟩ :
      StrictChart B (1 + k)) -
    objectClass (⟨D.source, h⟩ : StrictChart B (1 + k))

theorem equivalence_strictGenerator (D : AnnularDatum B k) (h : InfinityFree D.chart) :
    equivalence B (strictGenerator D h) = D.generator := by
  rw [AnnularDatum.generator_eq, strictGenerator, map_sub, map_add, equivalence_objectClass,
    equivalence_objectClass, equivalence_objectClass]
  rfl

variable (B) in
/-- Notation 4.17's `J_var` on `∞`-free charts: spanned by the strict generators. -/
def strictAnnularIdeal : Ideal (StrictRing B) :=
  Ideal.span {x | ∃ k, ∃ D : AnnularDatum B k, ∃ h : InfinityFree D.chart, x = strictGenerator D h}

/-! ### Splitting a datum by `∞`-patterns -/

/-- A chart splits along the `∞`-patterns of any reindexing of its coordinates. -/
theorem bclass_preimage_pieces {n m : ℕ} (E : Data B n k) (hE : DomainBounded E.toChart)
    (π : Fin m → Fin n) :
    bclass E = ∑ p : Finset (Fin m), bclass (inside E {w | w ∘ π ∈ patternSet p ∧
      w ∈ sortedUniverse (fun _ : Fin n => SortTag.rv)}
      ((patternSet_definable B p).preimage_real (fun _ : Fin n => SortTag.rv) π)) := by
  refine sum_cover bclass (fun x => DomainBounded x.toChart) (fun a c h hc => bounded_mono h hc)
    bclass_empty bclass_add _ Finset.univ E hE (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_
  · intro i _ j _ hne
    exact Set.disjoint_left.mpr (fun u hu hv => hne (pattern_unique hu.2.1 hv.2.1))
  · ext u
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · intro hu
      have hs := E.domain_definable.proper u hu
      exact ⟨zeroLocus (u ∘ π), hu, mem_patternSet_zeroLocus (u ∘ π) (fun i => hs (π i)), hs⟩
    · rintro ⟨p, hu, _⟩
      exact hu

theorem bclass_iso' {n m : ℕ} {D : Data B n (1 + k)} (E : Data B m (1 + k)) (F : Iso D.toChart E.toChart)
    (hD : DomainBounded D.toChart) (hE : DomainBounded E.toChart) : bclass D = bclass E :=
  bclass_iso hD hE F

section Pieces
variable (D : AnnularDatum B k) (p : Finset (Fin D.chart.arity))

theorem source_piece :
    bclass (piece (ofChart D.chart) p) = RVBoundedRing.objectClass (stripDatum D p).source := by
  rw [bclass_iso' _ (stripIso (ofChart D.chart) p) (bounded_mono (E := ofChart D.chart) (fun _ hu => hu.1) D.bounded)
    (strip_bounded (ofChart D.chart) D.bounded p), bclass_eq (strip_bounded (ofChart D.chart) D.bounded p)]
  rfl

/-- The endpoint over the `p`-part is isomorphic to the endpoint of the strip datum. -/
def endpointPieceIso :
    Iso (inside (ofChart (endpointChart D.chart D.coordinate D.finite D.aperture))
      {w | w ∘ headIndex 1 D.chart.arity ∈ patternSet p ∧
        w ∈ sortedUniverse (fun _ : Fin (1 + D.chart.arity) => SortTag.rv)}
      ((patternSet_definable B p).preimage_real _ (headIndex 1 D.chart.arity))).toChart
      (endpointChart (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite (stripDatum D p).aperture) := by
  apply RVCoordinateMaps.coordinateIso _ _ (coordIndex 1 p)
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      change w ∘ coordIndex 1 p ∈ RVDefinableGraphExtension.domain (stripChart D p)
        (fun v => D.aperture.aperture (unstrip p v))
      rw [strip_graph_eq]
      exact ⟨w, ⟨hw.1, hw.2⟩, rfl⟩
    · intro w hw w' hw' he
      have hh : (w ∘ headIndex 1 D.chart.arity) ∘ stripIndex p = (w' ∘ headIndex 1 D.chart.arity) ∘ stripIndex p := by
        funext i
        have := congrFun he (headIndex 1 (stripArity p) i)
        simpa only [Function.comp_apply, coordIndex_head] using this
      have hx := strip_injOn p hw.2.1 hw'.2.1 hh
      rw [graph_canonical D.chart D.aperture hw.1, graph_canonical D.chart D.aperture hw'.1, hx]
    · intro v hv
      have hv' : v ∈ RVDefinableGraphExtension.domain (stripChart D p)
          (fun v => D.aperture.aperture (unstrip p v)) := hv
      rw [strip_graph_eq] at hv'
      obtain ⟨w, hw, rfl⟩ := hv'
      exact ⟨w, hw, rfl⟩
  · intro w hw
    have h1 : (w ∘ coordIndex 1 p) ∘ headIndex 1 (stripArity p) =
        (w ∘ headIndex 1 D.chart.arity) ∘ stripIndex p :=
      funext (fun i => congrArg w (coordIndex_head 1 p i))
    have h2 : unstrip p ((w ∘ headIndex 1 D.chart.arity) ∘ stripIndex p) = w ∘ headIndex 1 D.chart.arity :=
      unstrip_comp hw.2.1
    have h3 : (w ∘ coordIndex 1 p) (aIdx (stripChart D p)) = w (aIdx D.chart) :=
      congrArg w (coordIndex_tail 1 p 0)
    change D.chart.volume (w ∘ headIndex 1 D.chart.arity) *
        ∏ l, codeValue (blownCoordinate D.chart D.coordinate (w ∘ headIndex 1 D.chart.arity) (w (aIdx D.chart)) l) =
      D.chart.volume (unstrip p ((w ∘ coordIndex 1 p) ∘ headIndex 1 (stripArity p))) *
        ∏ l, codeValue (blownCoordinate D.chart D.coordinate
          (unstrip p ((w ∘ coordIndex 1 p) ∘ headIndex 1 (stripArity p))) ((w ∘ coordIndex 1 p) (aIdx (stripChart D p))) l)
    rw [h1, h2, h3]

theorem endpoint_piece :
    bclass (inside (ofChart (endpointChart D.chart D.coordinate D.finite D.aperture))
      {w | w ∘ headIndex 1 D.chart.arity ∈ patternSet p ∧
        w ∈ sortedUniverse (fun _ : Fin (1 + D.chart.arity) => SortTag.rv)}
      ((patternSet_definable B p).preimage_real _ (headIndex 1 D.chart.arity))) =
      RVBoundedRing.objectClass (endpointBounded (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
        (stripDatum D p).aperture (stripDatum D p).bounded) := by
  have hb := endpoint_domain_bounded (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
    (stripDatum D p).aperture (stripDatum D p).bounded
  rw [bclass_iso' (ofChart (endpointChart (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
      (stripDatum D p).aperture)) (endpointPieceIso D p)
    (bounded_mono (E := ofChart (endpointChart D.chart D.coordinate D.finite D.aperture)) (fun _ hu => hu.1)
      (endpoint_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded)) hb,
    bclass_eq (D := ofChart (endpointChart (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
      (stripDatum D p).aperture)) hb]
  rfl

/-- The shell over the `p`-part is isomorphic to the shell of the strip datum. -/
def shellPieceIso :
    Iso (inside (ofChart (shellChart D.chart D.coordinate D.finite D.aperture))
      {w | w ∘ xIdx D.chart ∈ patternSet p ∧
        w ∈ sortedUniverse (fun _ : Fin (1 + (1 + D.chart.arity)) => SortTag.rv)}
      ((patternSet_definable B p).preimage_real _ (xIdx D.chart))).toChart
      (shellChart (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite (stripDatum D p).aperture) := by
  have hnz := graph_aperture_nonzero (stripDatum D p).chart (stripDatum D p).aperture
  have hgr : ∀ g ∈ (graphChart D.chart D.aperture).domain, g ∘ headIndex 1 D.chart.arity ∈ patternSet p →
      g ∘ coordIndex 1 p ∈ (graphChart (stripDatum D p).chart (stripDatum D p).aperture).domain := by
    intro g hg hp
    change g ∘ coordIndex 1 p ∈ RVDefinableGraphExtension.domain (stripChart D p)
      (fun v => D.aperture.aperture (unstrip p v))
    rw [strip_graph_eq]
    exact ⟨g, ⟨hg, hp, (graphChart D.chart D.aperture).domain_definable.proper g hg⟩, rfl⟩
  have hap : ∀ g : Fin (1 + D.chart.arity) → M,
      (g ∘ coordIndex 1 p) (aIdx (stripDatum D p).chart) = g (aIdx D.chart) :=
    fun g => congrArg g (coordIndex_tail 1 p 0)
  apply RVCoordinateMaps.coordinateIso _ _ (shellIndex p)
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨hg, hz, h1, h2⟩ := shell_mem D.chart D.aperture hw.1
      have hw' : w = join 1 (1 + D.chart.arity) (w ∘ headIndex 1 (1 + D.chart.arity))
          (w ∘ tailIndex 1 (1 + D.chart.arity)) := (join_reconstruct _ _ w).symm
      change w ∘ shellIndex p ∈ shellDomain (stripDatum D p).chart (stripDatum D p).aperture
      rw [hw', join_shellIndex]
      refine (VariableApertureRayCancellation.annularChart_join_iff _ _ hnz _ _).mpr
        ⟨hgr _ hg hw.2.1, hz, h1, ?_⟩
      rw [hap]
      exact h2
    · intro w hw w' hw' he
      have hx : (w ∘ xIdx D.chart) ∘ stripIndex p = (w' ∘ xIdx D.chart) ∘ stripIndex p := by
        funext i
        have := congrFun he (xIdx (stripDatum D p).chart i)
        change w (shellIndex p (headIndex 1 (1 + stripArity p) (headIndex 1 (stripArity p) i))) =
          w' (shellIndex p (headIndex 1 (1 + stripArity p) (headIndex 1 (stripArity p) i))) at this
        rw [shellIndex_head, coordIndex_head] at this
        exact this
      have hs : w (sIdx D.chart) = w' (sIdx D.chart) := by
        have := congrFun he (sIdx (stripDatum D p).chart)
        change w (shellIndex p (tailIndex 1 (1 + stripArity p) 0)) =
          w' (shellIndex p (tailIndex 1 (1 + stripArity p) 0)) at this
        rw [shellIndex_tail] at this
        exact this
      have hxx := strip_injOn p hw.2.1 hw'.2.1 hx
      rw [shell_canonical D.chart D.aperture hw.1, shell_canonical D.chart D.aperture hw'.1, hxx, hs]
    · intro v hv
      obtain ⟨hg', hz, h1, h2⟩ := shell_mem (stripDatum D p).chart (stripDatum D p).aperture hv
      have hg'' : v ∘ headIndex 1 (1 + stripArity p) ∈ RVDefinableGraphExtension.domain (stripChart D p)
          (fun v => D.aperture.aperture (unstrip p v)) := hg'
      rw [strip_graph_eq] at hg''
      obtain ⟨g, ⟨hg, hp, _⟩, hge⟩ := hg''
      change g ∘ coordIndex 1 p = v ∘ headIndex 1 (1 + stripArity p) at hge
      let w := join 1 (1 + D.chart.arity) g (v ∘ tailIndex 1 (1 + stripArity p))
      have hwmem : w ∈ shellDomain D.chart D.aperture := by
        refine (VariableApertureRayCancellation.annularChart_join_iff _ _
          (graph_aperture_nonzero D.chart D.aperture) _ _).mpr ⟨hg, hz, h1, ?_⟩
        rw [← hap g, hge]
        exact h2
      have hwx : w ∘ xIdx D.chart = g ∘ headIndex 1 D.chart.arity := by
        funext i
        change join 1 (1 + D.chart.arity) g (v ∘ tailIndex 1 (1 + stripArity p))
          (headIndex 1 (1 + D.chart.arity) (headIndex 1 D.chart.arity i)) = g (headIndex 1 D.chart.arity i)
        rw [join_head]
      refine ⟨w, ⟨hwmem, by rw [hwx]; exact hp,
        (shellChart D.chart D.coordinate D.finite D.aperture).domain_definable.proper w hwmem⟩, ?_⟩
      change join 1 (1 + D.chart.arity) g (v ∘ tailIndex 1 (1 + stripArity p)) ∘ shellIndex p = v
      rw [join_shellIndex, hge]
      exact join_reconstruct _ _ v
  · intro w hw
    have h1 : (w ∘ shellIndex p) ∘ xIdx (stripDatum D p).chart = (w ∘ xIdx D.chart) ∘ stripIndex p := by
      funext i
      change w (shellIndex p (headIndex 1 (1 + stripArity p) (headIndex 1 (stripArity p) i))) =
        w (headIndex 1 (1 + D.chart.arity) (headIndex 1 D.chart.arity (stripIndex p i)))
      rw [shellIndex_head, coordIndex_head]
    have h2 : unstrip p ((w ∘ xIdx D.chart) ∘ stripIndex p) = w ∘ xIdx D.chart := unstrip_comp hw.2.1
    have h3 : (w ∘ shellIndex p) (sIdx (stripDatum D p).chart) = w (sIdx D.chart) :=
      congrArg w (shellIndex_tail p 0)
    change D.chart.volume (w ∘ xIdx D.chart) *
        ∏ l, codeValue (blownCoordinate D.chart D.coordinate (w ∘ xIdx D.chart) (w (sIdx D.chart)) l) =
      D.chart.volume (unstrip p ((w ∘ shellIndex p) ∘ xIdx (stripDatum D p).chart)) *
        ∏ l, codeValue (blownCoordinate D.chart D.coordinate
          (unstrip p ((w ∘ shellIndex p) ∘ xIdx (stripDatum D p).chart)) ((w ∘ shellIndex p) (sIdx (stripDatum D p).chart)) l)
    rw [h1, h2, h3]

theorem shell_piece :
    bclass (inside (ofChart (shellChart D.chart D.coordinate D.finite D.aperture))
      {w | w ∘ xIdx D.chart ∈ patternSet p ∧
        w ∈ sortedUniverse (fun _ : Fin (1 + (1 + D.chart.arity)) => SortTag.rv)}
      ((patternSet_definable B p).preimage_real _ (xIdx D.chart))) =
      RVBoundedRing.objectClass (shellBounded (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
        (stripDatum D p).aperture (stripDatum D p).bounded) := by
  have hb := shell_domain_bounded (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
    (stripDatum D p).aperture (stripDatum D p).bounded
  rw [bclass_iso' (ofChart (shellChart (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
      (stripDatum D p).aperture)) (shellPieceIso D p)
    (bounded_mono (E := ofChart (shellChart D.chart D.coordinate D.finite D.aperture)) (fun _ hu => hu.1)
      (shell_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded)) hb,
    bclass_eq (D := ofChart (shellChart (stripDatum D p).chart (stripDatum D p).coordinate (stripDatum D p).finite
      (stripDatum D p).aperture)) hb]
  rfl

end Pieces

/-- Every Notation 4.17 generator is the sum of the generators of its `∞`-free strips. -/
theorem generator_eq_sum_strip (D : AnnularDatum B k) :
    D.generator = ∑ p : Finset (Fin D.chart.arity), (stripDatum D p).generator := by
  have hS : RVBoundedRing.objectClass (sourceBounded D.chart D.bounded) =
      ∑ p, RVBoundedRing.objectClass (sourceBounded (stripDatum D p).chart (stripDatum D p).bounded) := by
    rw [← bclass_ofChart (sourceBounded D.chart D.bounded)]
    change bclass (ofChart D.chart) = _
    rw [bclass_pieces (ofChart D.chart) D.bounded]
    exact Finset.sum_congr rfl (fun p _ => source_piece D p)
  have hE : RVBoundedRing.objectClass (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded) =
      ∑ p, RVBoundedRing.objectClass (endpointBounded (stripDatum D p).chart (stripDatum D p).coordinate
        (stripDatum D p).finite (stripDatum D p).aperture (stripDatum D p).bounded) := by
    rw [← bclass_ofChart (endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)]
    change bclass (ofChart (endpointChart D.chart D.coordinate D.finite D.aperture)) = _
    rw [bclass_preimage_pieces (ofChart (endpointChart D.chart D.coordinate D.finite D.aperture))
      (endpoint_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded) (headIndex 1 D.chart.arity)]
    exact Finset.sum_congr rfl (fun p _ => endpoint_piece D p)
  have hSh : RVBoundedRing.objectClass (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded) =
      ∑ p, RVBoundedRing.objectClass (shellBounded (stripDatum D p).chart (stripDatum D p).coordinate
        (stripDatum D p).finite (stripDatum D p).aperture (stripDatum D p).bounded) := by
    rw [← bclass_ofChart (shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)]
    change bclass (ofChart (shellChart D.chart D.coordinate D.finite D.aperture)) = _
    rw [bclass_preimage_pieces (ofChart (shellChart D.chart D.coordinate D.finite D.aperture))
      (shell_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded) (xIdx D.chart)]
    exact Finset.sum_congr rfl (fun p _ => shell_piece D p)
  simp only [AnnularDatum.generator_eq]
  rw [hS, hE, hSh, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-! ### The strict `J_var` corresponds to `manuscriptIdeal` -/

theorem generator_mem_map (D : AnnularDatum B k) :
    D.generator ∈ Ideal.map (equivalence B) (strictAnnularIdeal B) := by
  rw [generator_eq_sum_strip D]
  refine Ideal.sum_mem _ (fun p _ => ?_)
  rw [← equivalence_strictGenerator (stripDatum D p) (stripDatum_infinityFree D p)]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, _, _, rfl⟩)

variable (B) in
/-- Definition 4.9 and Notation 4.17: the strict `J_var`, spanned by generators with
`∞`-free representatives, maps exactly onto `manuscriptIdeal B`. -/
theorem map_strictAnnularIdeal :
    Ideal.map (RVStrictBoundedComparison.equivalence B) (strictAnnularIdeal B) =
      RelativeAnnularGenerators.manuscriptIdeal B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨k, D, h, rfl⟩
    change equivalence B (strictGenerator D h) ∈ RelativeAnnularGenerators.manuscriptIdeal B
    rw [equivalence_strictGenerator]
    exact Ideal.subset_span ⟨k, D, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨k, D, rfl⟩
    exact generator_mem_map D

variable (B) in
/-- The strict `J_var` is the transported ideal `strictManuscriptIdeal`. -/
theorem strictAnnularIdeal_eq :
    strictAnnularIdeal B = RVStrictBoundedCompatibility.strictManuscriptIdeal B := by
  rw [RVStrictBoundedCompatibility.strictManuscriptIdeal, ← map_strictAnnularIdeal B]
  exact (Ideal.comap_map_of_bijective _ (equivalence B).bijective).symm

end DiamondIntegral.Section4.RVStrictAnnularGenerators
