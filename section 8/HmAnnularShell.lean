import «section 8».HmAnnularEndpoint
import «section 4».VariableApertureAnnularDomains

/-! Lemma 8.3, third part: the shell of an annular generator.

The shell chart has points `(x, τ x, s)` with `x` in the source and `1 < value(s) ≤ γ(x)`, and
weight `ω(x) value(s)`. Its lattice part lies over the lattice part of the source with `s` a
lattice point (`shell_lattice`). For a piece `piece w g`, with `g = π^{M/m}`, and `1 ≤ i ≤ M`,
the slice `shellPiece w g i` of points over the piece with `value(s) = π^{i/m}` has the class of
the piece times the torus class (`shell_pieceClass`), and the lattice part of the shell of a given
weight is the disjoint union of such slices (`shell_fibre`). -/

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
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators RVMeasuredProductProperties
open RVRealProducts

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-! ### Rational powers of `π` are ordered like their exponents -/

theorem qpow_le_iff {a b : ℚ} : qpow π a ≤ qpow π b ↔ a ≤ b := by
  rw [← ι_le_iff, ι_qpow, ι_qpow]
  exact smul_le_smul_iff_of_pos_right (pos_ι_of_one_lt (one_lt_uniformizerValue P))

theorem qpow_lt_iff {a b : ℚ} : qpow π a < qpow π b ↔ a < b := by
  rw [← ι_lt_iff, ι_qpow, ι_qpow]
  exact smul_lt_smul_iff_of_pos_right (pos_ι_of_one_lt (one_lt_uniformizerValue P))

theorem qpow_zero' : qpow π 0 = 1 := by
  have := qpow_intCast π 0
  simpa using this

variable {k : ℕ} (D : AnnularDatum (base P) k) (m : ℕ+)

/-! ### The level of an aperture value -/

/-- The level `M` of an aperture value `g = π^{M/m}`. -/
def level (g : Γ) : ℕ := ⌊(m : ℚ) * ratValue π g⌋₊

theorem apValue_eq_level {g : Γ} (hg : g ∈ apValues P D m) :
    g = qpow π ((level P m g : ℚ) / (m : ℕ)) := by
  obtain ⟨z, hz⟩ := eq_qpow_of_inLattice m.ne_zero (apValue_lattice P D m hg)
  have hz0 : 0 ≤ z := by
    have h1 := one_le_apValue P D m hg
    rw [hz, ← qpow_zero' P, qpow_le_iff] at h1
    have hm : (0 : ℚ) < (m : ℕ) := by exact_mod_cast m.pos
    have := (div_nonneg_iff.mp h1)
    rcases this with ⟨h, _⟩ | ⟨_, h⟩
    · exact_mod_cast h
    · exact absurd h (not_le.mpr hm)
  have hm : ((m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr m.ne_zero
  have hr : ratValue π g = (z : ℚ) / (m : ℕ) := by rw [hz, ratValue_qpow (one_lt_uniformizerValue P)]
  have hl : (level P m g : ℚ) = z := by
    rw [level, hr, mul_div_cancel₀ _ hm]
    have : ((z : ℚ)) = ((z.toNat : ℕ) : ℚ) := by exact_mod_cast (Int.toNat_of_nonneg hz0).symm
    rw [this, Nat.floor_natCast]
  rw [hl]; exact hz

/-! ### The shell chart -/

/-- The shell chart. -/
abbrev shC : Chart (base P) (1 + k) := shellChart D.chart D.coordinate D.finite D.aperture

theorem shC_bounded : RVMeasuredBounds.DomainBounded (shC P D) :=
  shell_domain_bounded D.chart D.coordinate D.finite D.aperture D.bounded

theorem shell_aperture {u : Fin (1 + (1 + D.chart.arity)) → P.N} (hu : u ∈ (shC P D).domain) :
    (u ∘ headIndex 1 (1 + D.chart.arity)) (aIdx D.chart) = D.aperture.aperture (u ∘ xIdx D.chart) :=
  graph_aperture D.chart D.aperture (shell_mem D.chart D.aperture hu).1

theorem shell_lattice (u : Fin (1 + (1 + D.chart.arity)) → P.N) :
    u ∈ latticeDomain P (shC P D) m ↔
      u ∈ (shC P D).domain ∧ u ∘ xIdx D.chart ∈ latticeDomain P D.chart m ∧
        InLattice π m (codeValue (u (sIdx D.chart))) := by
  constructor
  · rintro ⟨hu, hl⟩
    exact ⟨hu, ⟨(shell_points D.chart D.aperture hu).1, fun i => hl _⟩, hl _⟩
  · rintro ⟨hu, hx, hs⟩
    refine ⟨hu, GammaBoundedProducts.all_coordinates 1 (1 + D.chart.arity)
      (fun t => InLattice π m (codeValue t)) u ?_ fun l => ?_⟩
    · refine GammaBoundedProducts.all_coordinates 1 D.chart.arity
        (fun t => InLattice π m (codeValue t)) (u ∘ headIndex 1 (1 + D.chart.arity)) hx.2 fun l => ?_
      fin_cases l
      change InLattice π m (codeValue ((u ∘ headIndex 1 (1 + D.chart.arity)) (aIdx D.chart)))
      rw [shell_aperture P D hu]
      exact aperture_lattice P D m hx
    · fin_cases l
      exact hs

/-- The slice of the shell over a piece, at the lattice point `π^{i/m}`. -/
def shellPiece (w g : Γ) (i : ℕ) : Set (Fin (1 + (1 + D.chart.arity)) → P.N) :=
  {u | u ∈ (shC P D).domain ∧ u ∘ xIdx D.chart ∈ piece P D m w g ∧
    codeValue (u (sIdx D.chart)) = qpow π ((i : ℚ) / (m : ℕ))}

theorem shellPiece_definable {g : Γ} (w : Γ) (hg : g ∈ apValues P D m) (i : ℕ) :
    DefinableOverBase (base P) (fun _ : Fin (1 + (1 + D.chart.arity)) => .rv) (shellPiece P D m w g i) := by
  have h1 := DefinableOverBase.inter (shC P D).domain_definable
    ((piece_definable P D m w hg).preimage_real (fun _ : Fin (1 + (1 + D.chart.arity)) => .rv)
      (xIdx D.chart))
  have hU : DefinableOverBase (base P) (fun _ : Fin (1 + (1 + D.chart.arity)) => .rv)
      ((shC P D).domain ∩ {u | u ∘ xIdx D.chart ∈ piece P D m w g ∧
        u ∈ sortedUniverse (fun _ : Fin (1 + (1 + D.chart.arity)) => SortTag.rv)}) := h1
  have h := preimage_definable (base P) hU (coord_volume_definable (base P) hU (sIdx D.chart))
    (qpow_definable P ((i : ℚ) / (m : ℕ)))
  convert h using 1
  refine Set.ext fun u => ?_
  change (u ∈ (shC P D).domain ∧ u ∘ xIdx D.chart ∈ piece P D m w g ∧ _) ↔ ((_ ∧ _ ∧ _) ∧ _)
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, (shC P D).domain_definable.proper u h1⟩, h3⟩,
    fun ⟨⟨h1, h2, _⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

theorem shellPiece_subset {w g : Γ} (i : ℕ) :
    shellPiece P D m w g i ⊆ latticeFibre P (shC P D) m (w * qpow π ((i : ℚ) / (m : ℕ))) := by
  rintro u ⟨hu, hx, hs⟩
  refine ⟨(shell_lattice P D m u).mpr ⟨hu, hx.1, ?_⟩, ?_⟩
  · rw [hs]; exact inLattice_qpow _ _ m.ne_zero
  · change (shellChart D.chart D.coordinate D.finite D.aperture).correctedWeight u = _
    rw [shell_weight D.chart D.coordinate D.finite D.aperture u hu, hx.2.1, hs]

/-- The coordinate map `u ↦ (x, s)` of the shell. -/
abbrev shellProj : Fin (1 + D.chart.arity) → Fin (1 + (1 + D.chart.arity)) :=
  join 1 D.chart.arity (xIdx D.chart) ![sIdx D.chart]

theorem shellProj_head (u : Fin (1 + (1 + D.chart.arity)) → P.N) :
    (u ∘ shellProj P D) ∘ headIndex 1 D.chart.arity = u ∘ xIdx D.chart :=
  funext fun i => by simp [Function.comp, join_head]

theorem shellProj_tail (u : Fin (1 + (1 + D.chart.arity)) → P.N) :
    (u ∘ shellProj P D) ∘ tailIndex 1 D.chart.arity = ![u (sIdx D.chart)] := by
  funext l; fin_cases l; simp [Function.comp, join_tail]

theorem torus_fibre_domain (α : Γ) (hα : GammaDefinableClosureAtBase (base P) α) (z : Fin 1 → P.N) :
    z ∈ (RESFibreObjects.fibre (base P) α 1 hα (GammaGroupNames.one_definable_base _)).domain ↔
      Proper z ∧ codeValue (z 0) = α := Iff.rfl

/-- **The shell slices.** A slice has the class of the piece times the class of a torus fibre. -/
theorem shell_pieceClass {w g : Γ} (hg : g ∈ apValues P D m) {i : ℕ} (hi1 : 1 ≤ i)
    (hiM : i ≤ level P m g) :
    classOn (fibreChart P (shC P D) (shC_bounded P D) m (w * qpow π ((i : ℚ) / (m : ℕ))))
        (shellPiece P D m w g i) =
      pieceClass P D m w g *
        nativeRESChartClass (RESFibreObjects.fibre (base P) (qpow π ((i : ℚ) / (m : ℕ))) 1
          (qpow_definable P _) (GammaGroupNames.one_definable_base _)) := by
  have hsubS : shellPiece P D m w g i ⊆
      (fibreChart P (shC P D) (shC_bounded P D) m (w * qpow π ((i : ℚ) / (m : ℕ)))).domain :=
    fun u hu => by rw [fibreChart_domain]; exact shellPiece_subset P D m i hu
  have hsubR : piece P D m w g ⊆ (fibreChart P D.chart D.bounded m w).domain :=
    fun x hx => by rw [fibreChart_domain]; exact piece_subset_fibre P D m w g hx
  rw [pieceClass, classOn_eq _ _ (shellPiece_definable P D m w hg i) hsubS,
    classOn_eq _ _ (piece_definable P D m w hg) hsubR, ← nativeRESChartClass_product]
  refine nativeRESChartClass_iso _ _ (RVUnderlyingIsomorphisms.ofMap _ _
    (fun u => u ∘ shellProj P D)
    (RVCoordinateMaps.coordinate_graph_definable (base P) _ (shellPiece_definable P D m w hg i) _)
    ⟨fun u hu => ?_, fun u hu v hv h => ?_, fun z hz => ?_⟩)
  · change u ∈ shellPiece P D m w g i at hu
    change (u ∘ shellProj P D) ∘ headIndex 1 D.chart.arity ∈ piece P D m w g ∧
      (u ∘ shellProj P D) ∘ tailIndex 1 D.chart.arity ∈ (RESFibreObjects.fibre (base P) _ 1 _ _).domain
    rw [shellProj_head, shellProj_tail, torus_fibre_domain]
    exact ⟨hu.2.1, fun l => by fin_cases l; exact (shell_points D.chart D.aperture hu.1).2.1, hu.2.2⟩
  · change u ∈ shellPiece P D m w g i at hu
    change v ∈ shellPiece P D m w g i at hv
    change u ∘ shellProj P D = v ∘ shellProj P D at h
    have h1 : u ∘ xIdx D.chart = v ∘ xIdx D.chart := by
      funext l
      have := congrFun h (headIndex 1 D.chart.arity l)
      simpa [shellProj, join_head, xIdx] using this
    have h2 : u (sIdx D.chart) = v (sIdx D.chart) := by
      have := congrFun h (tailIndex 1 D.chart.arity 0)
      simpa [shellProj, join_tail] using this
    rw [shell_canonical D.chart D.aperture hu.1, shell_canonical D.chart D.aperture hv.1, h1, h2]
  · change z ∘ headIndex 1 D.chart.arity ∈ piece P D m w g ∧
      z ∘ tailIndex 1 D.chart.arity ∈ (RESFibreObjects.fibre (base P) _ 1 _ _).domain at hz
    rw [torus_fibre_domain] at hz
    obtain ⟨hx, hzp, hzv⟩ := hz
    set x := z ∘ headIndex 1 D.chart.arity
    let u : Fin (1 + (1 + D.chart.arity)) → P.N :=
      join 1 (1 + D.chart.arity) (join 1 D.chart.arity x (apMap P D x)) (z ∘ tailIndex 1 D.chart.arity)
    have hux : u ∘ xIdx D.chart = x := funext fun l => by simp [u, xIdx, join_head]
    have hus : u (sIdx D.chart) = z (tailIndex 1 D.chart.arity 0) := by simp [u, sIdx, join_tail]
    have hgx : gam P D x = g := hx.2.2
    have hgraph : join 1 D.chart.arity x (apMap P D x) ∈ (graphChart D.chart D.aperture).domain :=
      join_mem_graphOn P (apMap P D) hx.1.1
    have hdom : u ∈ (shC P D).domain := by
      refine (VariableApertureRayCancellation.annularChart_join_iff (graphChart D.chart D.aperture)
        (aIdx D.chart) (graph_aperture_nonzero D.chart D.aperture) _ _).mpr ⟨hgraph, hzp, ?_, ?_⟩
      · refine lt_of_lt_of_eq ?_ hzv.symm
        rw [← qpow_zero' P, qpow_lt_iff]
        have hm : (0 : ℚ) < (m : ℕ) := by exact_mod_cast m.pos
        exact div_pos (by exact_mod_cast hi1) hm
      · refine hzv.trans_le ?_
        have ha : (join 1 D.chart.arity x (apMap P D x)) (aIdx D.chart) = D.aperture.aperture x := by
          simp [aIdx, join_tail]
        change _ ≤ codeValue ((join 1 D.chart.arity x (apMap P D x)) (aIdx D.chart))
        rw [ha]
        change _ ≤ gam P D x
        rw [hgx, apValue_eq_level P D m hg, qpow_le_iff]
        have hm : (0 : ℚ) < (m : ℕ) := by exact_mod_cast m.pos
        exact div_le_div_of_nonneg_right (by exact_mod_cast hiM) hm.le
    refine ⟨u, ⟨hdom, ?_, ?_⟩, ?_⟩
    · rw [hux]; exact hx
    · rw [hus]; exact hzv
    · change u ∘ shellProj P D = z
      have hh : (u ∘ shellProj P D) ∘ headIndex 1 D.chart.arity = z ∘ headIndex 1 D.chart.arity := by
        rw [shellProj_head, hux]
      have ht : (u ∘ shellProj P D) ∘ tailIndex 1 D.chart.arity = z ∘ tailIndex 1 D.chart.arity := by
        rw [shellProj_tail, hus]
        funext l; fin_cases l; rfl
      rw [← join_reconstruct 1 D.chart.arity (u ∘ shellProj P D), hh, ht, join_reconstruct]

end DiamondIntegral.Section8.Hm
