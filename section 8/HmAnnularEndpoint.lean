import «section 8».HmAnnularPieces

/-! Lemma 8.3, second part: the endpoint of an annular generator.

The endpoint chart has domain the graph `{(x, τ x)}` of the aperture over the source. Its weight
at `(x, τ x)` is `ω(x) γ(x)` (`endpoint_weight`), its lattice part lies over the lattice part of the
source (`endpoint_lattice`), and its lattice part of weight `w'` is the disjoint union of the
graphs over the pieces `piece w g` with `w g = w'`, each of which has the class of the piece
(`endpoint_pieceClass`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.ValueMaps
open DiamondIntegral.Section8.RESPieces
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

variable {k : ℕ} (D : AnnularDatum (base P) k) (m : ℕ+)

/-- The endpoint chart. -/
abbrev endC : Chart (base P) (1 + k) := endpointChart D.chart D.coordinate D.finite D.aperture

theorem endC_bounded : RVMeasuredBounds.DomainBounded (endC P D) :=
  endpoint_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded

theorem endpoint_weight (u : Fin (1 + D.chart.arity) → P.N) (hu : u ∈ (endC P D).domain) :
    (endC P D).correctedWeight u =
      D.chart.correctedWeight (u ∘ headIndex 1 D.chart.arity) * gam P D (u ∘ headIndex 1 D.chart.arity) := by
  have hx : u ∘ headIndex 1 D.chart.arity ∈ D.chart.domain := hu.1
  have ha : u (aIdx D.chart) = D.aperture.aperture (u ∘ headIndex 1 D.chart.arity) :=
    graph_aperture D.chart D.aperture hu
  unfold endC endpointChart
  rw [pieceChart_weight]
  simp only [Chart.correctedWeight]
  rw [prod_split D.coordinate, prod_split D.coordinate
      (fun l => codeValue (D.chart.coordinate (u ∘ headIndex 1 D.chart.arity) l)),
    blownCoordinate_at, ha,
    GammaGroupNames.codeValue_mul _ _ (D.aperture.nonzero _ hx) (D.chart.coordinate_proper _ hx _)]
  have hs : ∀ i, blownCoordinate D.chart D.coordinate (u ∘ headIndex 1 D.chart.arity)
      (D.aperture.aperture (u ∘ headIndex 1 D.chart.arity)) (skip D.coordinate i) =
      D.chart.coordinate (u ∘ headIndex 1 D.chart.arity) (skip D.coordinate i) := by
    intro i
    simp only [blownCoordinate, Function.update_of_ne (skip_ne D.coordinate i)]
  simp only [hs]
  ac_rfl

theorem endpoint_lattice (u : Fin (1 + D.chart.arity) → P.N) :
    u ∈ latticeDomain P (endC P D) m ↔
      u ∈ (endC P D).domain ∧ u ∘ headIndex 1 D.chart.arity ∈ latticeDomain P D.chart m := by
  constructor
  · rintro ⟨hu, hl⟩
    exact ⟨hu, hu.1, fun i => hl _⟩
  · rintro ⟨hu, hx⟩
    refine ⟨hu, GammaBoundedProducts.all_coordinates 1 D.chart.arity
      (fun t => InLattice π m (codeValue t)) u hx.2 fun l => ?_⟩
    fin_cases l
    change InLattice π m (codeValue (u (aIdx D.chart)))
    rw [graph_aperture D.chart D.aperture hu]
    exact aperture_lattice P D m hx

/-- The graph over a piece. -/
def endPiece (w g : Γ) : Set (Fin (1 + D.chart.arity) → P.N) :=
  {u | u ∈ (endC P D).domain ∧ u ∘ headIndex 1 D.chart.arity ∈ piece P D m w g}

theorem endPiece_definable {g : Γ} (w : Γ) (hg : g ∈ apValues P D m) :
    DefinableOverBase (base P) (fun _ : Fin (1 + D.chart.arity) => .rv) (endPiece P D m w g) := by
  have h := DefinableOverBase.inter (endC P D).domain_definable
    ((piece_definable P D m w hg).preimage_real (fun _ : Fin (1 + D.chart.arity) => .rv)
      (headIndex 1 D.chart.arity))
  convert h using 1
  all_goals try rfl
  refine Set.ext fun u => ?_
  change (u ∈ (endC P D).domain ∧ u ∘ headIndex 1 D.chart.arity ∈ piece P D m w g) ↔
    (u ∈ (endC P D).domain ∧ (u ∘ headIndex 1 D.chart.arity ∈ piece P D m w g ∧
      u ∈ sortedUniverse (fun _ : Fin (1 + D.chart.arity) => SortTag.rv)))
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, (endC P D).domain_definable.proper u h1⟩,
    fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩

theorem endPiece_subset {w g : Γ} : endPiece P D m w g ⊆ latticeFibre P (endC P D) m (w * g) := by
  rintro u ⟨hu, hx, hw, hg⟩
  refine ⟨(endpoint_lattice P D m u).mpr ⟨hu, hx⟩, ?_⟩
  rw [endpoint_weight P D u hu, hw, hg]

/-- The weight-`w'` lattice part of the endpoint is the union of the graphs over the pieces. -/
theorem endpoint_fibre (w' : Γ) :
    latticeFibre P (endC P D) m w' =
      ⋃ p ∈ (weights P D.chart D.bounded m ×ˢ apValues P D m).filter (fun p => p.1 * p.2 = w'),
        endPiece P D m p.1 p.2 := by
  ext u
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hl, hw⟩
    obtain ⟨hu, hx⟩ := (endpoint_lattice P D m u).mp hl
    refine ⟨(D.chart.correctedWeight (u ∘ headIndex 1 D.chart.arity), gam P D (u ∘ headIndex 1 D.chart.arity)),
      ⟨⟨(mem_weights P _ D.bounded m _).mpr ⟨_, hx, rfl⟩, (mem_apValues P D m _).mpr ⟨_, hx, rfl⟩⟩, ?_⟩,
      hu, hx, rfl, rfl⟩
    rw [← endpoint_weight P D u hu]; exact hw
  · rintro ⟨p, ⟨-, hp⟩, hu⟩
    have := endPiece_subset P D m hu
    rw [hp] at this
    exact this

theorem endPieces_disjoint (w' : Γ) :
    (((weights P D.chart D.bounded m ×ˢ apValues P D m).filter (fun p => p.1 * p.2 = w') :
      Finset (Γ × Γ)) : Set (Γ × Γ)).PairwiseDisjoint (fun p => endPiece P D m p.1 p.2) := by
  intro p _ q _ hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro u ⟨-, -, hp1, hp2⟩ ⟨-, -, hq1, hq2⟩
  exact hpq (Prod.ext (hp1.symm.trans hq1) (hp2.symm.trans hq2))

/-- **The endpoint pieces.** The graph over a piece has the class of the piece. -/
theorem endpoint_pieceClass {w g : Γ} (hg : g ∈ apValues P D m) :
    classOn (fibreChart P (endC P D) (endC_bounded P D) m (w * g)) (endPiece P D m w g) =
      pieceClass P D m w g := by
  have hsubE : endPiece P D m w g ⊆ (fibreChart P (endC P D) (endC_bounded P D) m (w * g)).domain :=
    fun u hu => by rw [fibreChart_domain]; exact endPiece_subset P D m hu
  have hsubR : piece P D m w g ⊆ (fibreChart P D.chart D.bounded m w).domain :=
    fun x hx => by rw [fibreChart_domain]; exact piece_subset_fibre P D m w g hx
  rw [pieceClass, classOn_eq _ _ (endPiece_definable P D m w hg) hsubE,
    classOn_eq _ _ (piece_definable P D m w hg) hsubR]
  refine nativeRESChartClass_iso _ _ (RVUnderlyingIsomorphisms.ofMap _ _
    (fun u => u ∘ headIndex 1 D.chart.arity)
    (RVCoordinateMaps.coordinate_graph_definable (base P) _ (endPiece_definable P D m w hg) _)
    ⟨fun u hu => hu.2, fun u hu v hv h => ?_, fun x hx => ⟨join 1 D.chart.arity x (apMap P D x), ?_, ?_⟩⟩)
  · change u ∈ endPiece P D m w g at hu
    change v ∈ endPiece P D m w g at hv
    rw [graph_canonical D.chart D.aperture hu.1, graph_canonical D.chart D.aperture hv.1]
    change u ∘ headIndex 1 D.chart.arity = v ∘ headIndex 1 D.chart.arity at h
    rw [h]
  · change x ∈ piece P D m w g at hx
    have hh : join 1 D.chart.arity x (apMap P D x) ∘ headIndex 1 D.chart.arity = x :=
      funext fun i => join_head _ _ _ _ i
    refine ⟨join_mem_graphOn P (apMap P D) hx.1.1, ?_⟩
    rw [hh]; exact hx
  · exact funext fun i => join_head _ _ _ _ i

end DiamondIntegral.Section8.Hm
