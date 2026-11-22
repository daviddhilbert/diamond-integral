import «section 8».MapLattice
import «section 8».HmLocalized
import «section 8».RESPieces
import «section 4».RelativeAnnularGenerators

/-! Lemma 8.3, first part: the pieces of the lattice part of the source of an annular generator.

For an annular datum `D` (a bounded chart `r`, a coordinate `j`, an aperture `τ`), let `L` be the
lattice part of `r` at level `m`, `ω` the weight of `r` and `γ(x) = codeValue (τ x)`.

* `aperture_lattice`: `γ` takes lattice values on `L` (definable maps preserve the lattice);
* `apValues`: the finitely many values of `γ` on `L` (orthogonality), each definable;
* `piece w g = {x ∈ L | ω x = w, γ x = g}`, definable;
* `class_source`: the class of the lattice part of `r` of weight `w` is the sum over `g` of the
  classes of the pieces. -/

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
open AnnularBlowup BlowupChart RelativeAnnularGenerators

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

variable {k : ℕ} (D : AnnularDatum (base P) k) (m : ℕ+)

/-- The aperture as a map to `RV¹`. -/
abbrev apMap (x : Fin D.chart.arity → P.N) : Fin 1 → P.N := ![D.aperture.aperture x]

theorem apGraph_definable :
    DefinableOverBase (base P) (fun _ : Fin (1 + D.chart.arity) => .rv) (graphOn D.chart.domain (apMap P D)) :=
  D.aperture.graph_definable

/-- The value of the aperture. -/
abbrev gam (x : Fin D.chart.arity → P.N) : Γ := codeValue (D.aperture.aperture x)

theorem aperture_lattice {x : Fin D.chart.arity → P.N} (hx : x ∈ latticeDomain P D.chart m) :
    InLattice π m (gam P D x) :=
  map_lattice P D.chart.domain_definable (apMap P D) (apGraph_definable P D) m hx.1 hx.2 0

theorem gam_volume : VolumeDefinable (base P) D.chart.domain (gam P D) :=
  map_coord_volume P D.chart.domain_definable (apMap P D) (apGraph_definable P D) 0

theorem latticeDomain_definable' :
    DefinableOverBase (base P) (fun _ : Fin D.chart.arity => .rv) (latticeDomain P D.chart m) :=
  latticeDomain_definable P (bdd P D.chart D.bounded) m.ne_zero

theorem apValues_finite : (gam P D '' latticeDomain P D.chart m).Finite := by
  obtain ⟨N, hN⟩ := chart_pow_bound P (bdd P D.chart D.bounded)
  have hL := latticeDomain_definable' P D m
  refine values_finite_of_volume P hL (volume_restrict (base P) (gam_volume P D) hL (fun _ h => h.1))
    (fun _ => {x | iRV x ∧ codeValue x ∈ latticeBox P m N}) (fun _ => ?_) (fun _ => ?_) ?_
  · have hU := BlowupChart.rv_universe_definable (base P) 1
    have h := preimage_definable (base P) hU (coord_volume_definable (base P) hU 0)
      (latticeBox_definable P m.ne_zero N)
    show DefinableOverBase (base P) (fun _ : Fin 1 => .rv)
      {z | z 0 ∈ {x : P.N | iRV x ∧ codeValue x ∈ latticeBox P m N}}
    convert h using 1
    refine Set.ext fun z => ?_
    change (iRV (z 0) ∧ codeValue (z 0) ∈ latticeBox P m N) ↔
      (z ∈ sortedUniverse (fun _ : Fin 1 => SortTag.rv) ∧ codeValue (z 0) ∈ latticeBox P m N)
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun j => by rw [Subsingleton.elim j 0]; exact h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1 0, h2⟩⟩
  · refine ((((latticeBox_finite P m.ne_zero N).image Subtype.val).insert Values.infinity)).subset ?_
    rintro x ⟨t, ht, rfl⟩
    by_cases h0 : t.val = iRVZero
    · exact Or.inl ((Values.vrv_eq_infinity_iff t).mpr h0)
    · right
      refine ⟨codeValue t.val, ht.2, ?_⟩
      have hf := RVMeasuredBounds.finiteValue_vrv t
      have hne : Values.vrv t ≠ Values.infinity := fun h => h0 ((Values.vrv_eq_infinity_iff t).mp h)
      rw [← hf]
      simp only [RVMeasuredBounds.finiteValue, hne, ne_eq, not_false_eq_true, ↓reduceDIte]
  · intro u hu i
    rw [latticeDomain_eq_box P (bdd P D.chart D.bounded) m N hN] at hu
    exact ⟨D.chart.domain_definable.proper u hu.1 i, hu.2 i⟩

/-- The aperture values on the lattice part. -/
def apValues : Finset Γ := (apValues_finite P D m).toFinset

theorem mem_apValues (g : Γ) :
    g ∈ apValues P D m ↔ ∃ x ∈ latticeDomain P D.chart m, gam P D x = g := by
  simp only [apValues, Set.Finite.mem_toFinset, Set.mem_image]

theorem apValue_definable {g : Γ} (hg : g ∈ apValues P D m) :
    GammaDefinableClosureAtBase (base P) g := by
  have hfin := apValues_finite P D m
  refine gamma_finset_element_definable_base (base P) hfin.toFinset ?_ g hg
  rw [hfin.coe_toFinset]
  exact image_definable (base P) (volume_restrict (base P) (gam_volume P D)
    (latticeDomain_definable' P D m) (fun _ h => h.1))

theorem apValue_lattice {g : Γ} (hg : g ∈ apValues P D m) : InLattice π m g := by
  obtain ⟨x, hx, rfl⟩ := (mem_apValues P D m g).mp hg
  exact aperture_lattice P D m hx

theorem one_le_apValue {g : Γ} (hg : g ∈ apValues P D m) : 1 ≤ g := by
  obtain ⟨x, hx, rfl⟩ := (mem_apValues P D m g).mp hg
  exact D.aperture.nonnegative x hx.1

/-- The piece of the lattice part with weight `w` and aperture value `g`. -/
def piece (w g : Γ) : Set (Fin D.chart.arity → P.N) :=
  {x | x ∈ latticeDomain P D.chart m ∧ D.chart.correctedWeight x = w ∧ gam P D x = g}

theorem piece_subset_fibre (w g : Γ) : piece P D m w g ⊆ latticeFibre P D.chart m w :=
  fun _ h => ⟨h.1, h.2.1⟩

theorem piece_definable {g : Γ} (w : Γ) (hg : g ∈ apValues P D m) :
    DefinableOverBase (base P) (fun _ : Fin D.chart.arity => .rv) (piece P D m w g) := by
  have hF := latticeFibre_definable' P D.chart D.bounded m w
  have h := preimage_definable (base P) hF (volume_restrict (base P) (gam_volume P D) hF
    (fun _ h => h.1.1)) (apValue_definable P D m hg)
  convert h using 1
  exact Set.ext fun x => ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- The class of the piece, inside the lattice part of weight `w`. -/
def pieceClass (w g : Γ) : RESDimensionFreeReduction.Ring (base P) :=
  classOn (fibreChart P D.chart D.bounded m w) (piece P D m w g)

theorem pieces_disjoint (w : Γ) :
    ((apValues P D m : Finset Γ) : Set Γ).PairwiseDisjoint (fun g => piece P D m w g) := by
  intro g _ g' _ hgg'
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨-, -, h1⟩ ⟨-, -, h2⟩
  exact hgg' (h1.symm.trans h2)

theorem fibre_eq_pieces (w : Γ) :
    latticeFibre P D.chart m w = ⋃ g ∈ apValues P D m, piece P D m w g := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hx, hw⟩
    exact ⟨gam P D x, (mem_apValues P D m _).mpr ⟨x, hx, rfl⟩, hx, hw, rfl⟩
  · rintro ⟨g, -, hx, hw, -⟩
    exact ⟨hx, hw⟩

/-- **The source.** The class of the lattice part of weight `w` is the sum of the classes of its
pieces. -/
theorem class_source (w : Γ) :
    nativeRESChartClass (fibreChart P D.chart D.bounded m w) =
      ∑ g ∈ apValues P D m, pieceClass P D m w g := by
  rw [← classOn_domain (fibreChart P D.chart D.bounded m w), fibreChart_domain, fibre_eq_pieces]
  exact classOn_biUnion _ _ _ (fun g hg => piece_definable P D m w hg)
    (fun g _ => fun x hx => by rw [fibreChart_domain]; exact piece_subset_fibre P D m w g hx)
    (pieces_disjoint P D m w)

end DiamondIntegral.Section8.Hm
