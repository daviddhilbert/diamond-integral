import «section 7».Lemma714Schema

/-! Lemma 7.14, part 3: schemata for restrictions and aperture data.

* `ChartSchema.restrict`: the restriction of a chart schema to a definable
  piece of its parameter-row space; validity passes to restrictions.
* `DatumSchema`: a uniform family of aperture data (Definition 7.2): a chart
  schema of degree `1 + k`, the blown-up coordinate `j`, the graph of the
  aperture `τ`, and a natural-number bound for the fibres of the inactive
  projection `pr_{~j}` (which makes "finite-to-one" first order). A valid row is
  a Section 4 `AnnularDatum` over `B ∪ z` (`DatumSchema.toDatum`), and the
  validity locus is definable (`DatumSchema.valid_definable`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks AnnularBlowup
open IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

/-! ### Restriction to a piece -/

namespace ChartSchema
variable {d : ℕ} (W : ChartSchema B sp d)

/-- The restriction of a chart schema to a definable piece `P` of `M^(p + a)`. -/
def restrict (P : Set (Fin (p + W.arity) → M)) (hP : DefinableOverBase B (Fin.append sp (rvs W.arity)) P) :
    ChartSchema B sp d where
  arity := W.arity
  domain := W.domain ∩ P
  domain_definable := W.domain_definable.inter hP
  coord := W.coord ∩ {w | w ∘ Fin.castAdd d ∈ P ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs W.arity)) (rvs d))}
  coord_definable := W.coord_definable.inter (hP.preimage_real _ (Fin.castAdd d))
  volume := W.volume ∩ {w | w ∘ Fin.castAdd 1 ∈ P ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs W.arity)) (rvs 1))}
  volume_definable := W.volume_definable.inter (hP.preimage_real _ (Fin.castAdd 1))
  bound := W.bound

variable {W} {P : Set (Fin (p + W.arity) → M)} {hP : DefinableOverBase B (Fin.append sp (rvs W.arity)) P}

theorem restrict_row (z : Fin p → M) : (W.restrict P hP).row z = W.row z ∩ {u | Fin.append z u ∈ P} := rfl

theorem restrict_coordRow (z : Fin p → M) (u : Fin W.arity → M) (y : Fin d → M) :
    (W.restrict P hP).coordRow z u y ↔ W.coordRow z u y ∧ Fin.append z u ∈ P := by
  unfold coordRow restrict
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, append_comp_castAdd]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, W.coord_definable.proper _ h.1⟩⟩

theorem restrict_volRow (z : Fin p → M) (u : Fin W.arity → M) (c : M) :
    (W.restrict P hP).volRow z u c ↔ W.volRow z u c ∧ Fin.append z u ∈ P := by
  unfold volRow restrict
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, append_comp_castAdd]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, W.volume_definable.proper _ h.1⟩⟩

/-- Validity passes to restrictions. -/
theorem Valid.restrict {z : Fin p → M} (hz : W.Valid z) : (W.restrict P hP).Valid z := by
  refine ⟨⟨hz.sorted, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro u ⟨hu, huP⟩
    obtain ⟨y, hy, huniq⟩ := hz.map.2.1 u hu
    refine ⟨y, (restrict_coordRow (W := W) (P := P) (hP := hP) z u y).mpr ⟨hy, huP⟩, fun y' hy' => huniq y' ?_⟩
    exact ((restrict_coordRow (hP := hP) z u y').mp hy').1
  · intro u y h
    have h' := (restrict_coordRow (hP := hP) z u y).mp h
    exact ⟨hz.map.2.2.1 u y h'.1, h'.2⟩
  · intro y hy
    obtain ⟨hfin, hle⟩ := hz.map.2.2.2 y hy
    have hsub : {x : Fin W.arity → M | Fin.append (Fin.append z x) y ∈ (W.restrict P hP).coord} ⊆
        {x | Fin.append (Fin.append z x) y ∈ W.coord} := fun x hx => hx.1
    exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hle⟩
  · intro u y h
    exact hz.proper u y ((restrict_coordRow (hP := hP) z u y).mp h).1
  · rintro u ⟨hu, huP⟩
    obtain ⟨c, hc⟩ := hz.vol_total u hu
    exact ⟨c, (restrict_volRow (W := W) (P := P) (hP := hP) z u c).mpr ⟨hc, huP⟩⟩
  · intro u c h
    have h' := (restrict_volRow (hP := hP) z u c).mp h
    obtain ⟨hu, hc⟩ := hz.vol_dom u c h'.1
    exact ⟨⟨hu, h'.2⟩, hc⟩
  · intro u c c' h hc hc'
    have h' := (restrict_volRow (hP := hP) z u c).mp h
    rw [restrict_volRow]
    constructor
    · rintro ⟨h1, -⟩
      exact (hz.vol_same u c c' h'.1 hc hc').mp h1
    · intro he
      exact ⟨(hz.vol_same u c c' h'.1 hc hc').mpr he, h'.2⟩
  · obtain ⟨lo, hi, hb⟩ := hz.bounded
    exact ⟨lo, hi, fun u hu => hb u hu.1⟩

end ChartSchema

/-! ### Aperture-datum schemata -/

/-- A uniform family of aperture data of Definition 7.2. -/
structure DatumSchema (B : Base (M := M)) {p : ℕ} (sp : Fin p → SortTag) (k : ℕ) where
  chart : ChartSchema B sp (1 + k)
  coordinate : Fin (1 + k)
  aperture : Set (Fin ((p + chart.arity) + 1) → M)
  aperture_definable : DefinableOverBase B (Fin.append (Fin.append sp (rvs chart.arity)) (rvs 1)) aperture
  inactiveBound : ℕ

namespace DatumSchema
variable {k : ℕ} (D : DatumSchema B sp k)

/-- The aperture row at `z`. -/
def apRow (z : Fin p → M) (u : Fin D.chart.arity → M) (t : M) : Prop :=
  Fin.append (Fin.append z u) (fun _ : Fin 1 => t) ∈ D.aperture

/-- `u` lies over the inactive value `t`: the structural map at `u` agrees with
`t` off the coordinate `j`. -/
def inactRel (z : Fin p → M) (u : Fin D.chart.arity → M) (t : Fin (1 + k) → M) : Prop :=
  ∃ s, D.chart.coordRow z u (Function.update t D.coordinate s)

/-- The row at `z` is an aperture datum. -/
structure Valid (z : Fin p → M) : Prop where
  chart : D.chart.Valid z
  ap_unique : ∀ u ∈ D.chart.row z, ∃! t, D.apRow z u t
  ap_dom : ∀ u t, D.apRow z u t → u ∈ D.chart.row z
  ap_value : ∀ u t, D.apRow z u t → NonzeroRV t ∧ 1 ≤ codeValue t
  ap_bounded : ∃ Δ : Values.Gamma (M := M), ∀ u t, D.apRow z u t → codeValue t ≤ Δ
  inactive : ∀ t : Fin (1 + k) → M, (∀ i, sortEval SortTag.rv (t i)) →
    {u | D.inactRel z u t}.Finite ∧ {u | D.inactRel z u t}.ncard ≤ D.inactiveBound

variable {D}

/-- The aperture at `z`, by choice on the row (`0` elsewhere). -/
def apAt (D : DatumSchema B sp k) (z : Fin p → M) (u : Fin D.chart.arity → M) : M :=
  if h : ∃ t, D.apRow z u t then h.choose else iRVZero

theorem apRow_apAt {z : Fin p → M} (hz : D.Valid z) {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.row z) :
    D.apRow z u (D.apAt z u) := by
  have h : ∃ t, D.apRow z u t := (hz.ap_unique u hu).exists
  rw [apAt, dif_pos h]
  exact h.choose_spec

theorem apRow_iff {z : Fin p → M} (hz : D.Valid z) (u : Fin D.chart.arity → M) (t : M) :
    D.apRow z u t ↔ u ∈ D.chart.row z ∧ D.apAt z u = t := by
  constructor
  · intro h
    have hu := hz.ap_dom u t h
    exact ⟨hu, (hz.ap_unique u hu).unique (apRow_apAt hz hu) h⟩
  · rintro ⟨hu, rfl⟩
    exact apRow_apAt hz hu

theorem aperture_graph_definable {z : Fin p → M} (hz : D.Valid z) :
    DefinableOverBase (baseAt B z) (fun _ : Fin (1 + D.chart.arity) => .rv)
      (RVDefinableGraphExtension.domain (D.chart.toChart z hz.chart) (D.apAt z)) := by
  have h := (row2_definable sp (rvs D.chart.arity) (rvs 1) D.aperture_definable z).preimage_real
    (fun _ : Fin (1 + D.chart.arity) => .rv) (ChartSchema.graphIndex D.chart.arity 1)
  convert h using 1
  ext w
  have key : (Fin.append (Fin.append z (fun i => (w ∘ ChartSchema.graphIndex D.chart.arity 1) (Fin.castAdd 1 i)))
      (fun j => (w ∘ ChartSchema.graphIndex D.chart.arity 1) (Fin.natAdd D.chart.arity j))) ∈ D.aperture ↔
      D.apRow z (w ∘ headIndex 1 D.chart.arity) (w (tailIndex 1 D.chart.arity 0)) := by
    unfold apRow
    have e : (fun j : Fin 1 => (w ∘ ChartSchema.graphIndex D.chart.arity 1) (Fin.natAdd D.chart.arity j)) =
        fun _ => w (tailIndex 1 D.chart.arity 0) := by
      funext j; fin_cases j; simp [ChartSchema.graphIndex]
    have e' : (fun i => (w ∘ ChartSchema.graphIndex D.chart.arity 1) (Fin.castAdd 1 i)) =
        w ∘ headIndex 1 D.chart.arity := by
      funext i; simp [ChartSchema.graphIndex]
    rw [e, e']
  change (w ∘ headIndex 1 D.chart.arity ∈ D.chart.row z ∧
      ![D.apAt z (w ∘ headIndex 1 D.chart.arity)] = w ∘ tailIndex 1 D.chart.arity) ↔
    (_ ∈ D.aperture ∧ w ∈ sortedUniverse _)
  rw [key, apRow_iff hz]
  have e2 : (![D.apAt z (w ∘ headIndex 1 D.chart.arity)] = w ∘ tailIndex 1 D.chart.arity) ↔
      D.apAt z (w ∘ headIndex 1 D.chart.arity) = w (tailIndex 1 D.chart.arity 0) := by
    constructor
    · intro he
      exact congrFun he 0
    · intro he
      funext j
      fin_cases j
      exact he
  rw [e2]
  constructor
  · rintro ⟨hu, he⟩
    refine ⟨⟨hu, he⟩, ?_⟩
    apply GammaBoundedProducts.all_coordinates 1 D.chart.arity (fun x => sortEval SortTag.rv x)
    · exact fun i => ChartSchema.row_rv hu i
    · intro i
      fin_cases i
      show sortEval SortTag.rv (w (tailIndex 1 D.chart.arity 0))
      rw [← he]
      exact (hz.ap_value _ _ (apRow_apAt hz hu)).1.1
  · rintro ⟨h, -⟩
    exact h

/-- The aperture of a valid row. -/
def toAperture {z : Fin p → M} (hz : D.Valid z) : Aperture (D.chart.toChart z hz.chart) where
  aperture := D.apAt z
  graph_definable := aperture_graph_definable hz
  nonzero := fun u hu => (hz.ap_value u _ (apRow_apAt hz hu)).1
  nonnegative := fun u hu => (hz.ap_value u _ (apRow_apAt hz hu)).2
  bound := hz.ap_bounded.choose
  bounded := fun u hu => hz.ap_bounded.choose_spec u _ (apRow_apAt hz hu)

theorem toChart_inactiveFinite {z : Fin p → M} (hz : D.Valid z) :
    InactiveFinite (D.chart.toChart z hz.chart) D.coordinate := by
  intro t
  by_cases hne : {u | u ∈ D.chart.row z ∧ inactive (D.chart.toChart z hz.chart) D.coordinate u = t}.Nonempty
  · obtain ⟨u₀, hu₀, ht₀⟩ := hne
    let t' := Function.update t D.coordinate (D.chart.coordAt z u₀ D.coordinate)
    have ht'rv : ∀ i, sortEval SortTag.rv (t' i) := by
      intro i
      by_cases hi : i = D.coordinate
      · subst hi
        simp only [t', Function.update_self]
        exact (ChartSchema.coordAt_proper hz.chart hu₀ _).1
      · simp only [t', Function.update_of_ne hi]
        rw [← ht₀]
        simp only [inactive, Function.update_of_ne hi]
        exact (ChartSchema.coordAt_proper hz.chart hu₀ i).1
    refine (hz.inactive t' ht'rv).1.subset ?_
    rintro u ⟨hu, ht⟩
    refine ⟨D.chart.coordAt z u D.coordinate, ?_⟩
    have he : Function.update t' D.coordinate (D.chart.coordAt z u D.coordinate) = D.chart.coordAt z u := by
      funext i
      by_cases hi : i = D.coordinate
      · subst hi
        simp
      · simp only [t', Function.update_of_ne hi]
        rw [← ht]
        simp only [inactive, Function.update_of_ne hi]
        rfl
    rw [he]
    exact ChartSchema.coordRow_coordAt hz.chart hu
  · refine Set.Finite.subset Set.finite_empty ?_
    intro u hu
    exact (hne ⟨u, hu⟩).elim

/-- **The aperture datum of a valid row**, over `B ∪ z`. -/
def toDatum {z : Fin p → M} (hz : D.Valid z) : RelativeAnnularGenerators.AnnularDatum (baseAt B z) k where
  chart := D.chart.toChart z hz.chart
  coordinate := D.coordinate
  finite := toChart_inactiveFinite hz
  aperture := toAperture hz
  bounded := ChartSchema.toChart_domainBounded hz.chart

end DatumSchema

end DiamondIntegral.Section7.Lemma714Schema
