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

/-! #### The validity locus of a datum schema is definable -/

section DatumDefinable
variable (D)

omit hM in
theorem existsUnique_fin_one (P : (Fin 1 → M) → Prop) :
    (∃! b : Fin 1 → M, P b) ↔ ∃! t : M, P (fun _ => t) := by
  have e : ∀ b : Fin 1 → M, b = fun _ => b 0 := fun b => by funext j; fin_cases j; rfl
  constructor
  · rintro ⟨b, hb, hu⟩
    refine ⟨b 0, by show P (fun _ => b 0); rw [← e b]; exact hb, fun t ht => ?_⟩
    have := hu _ ht
    rw [← this]
  · rintro ⟨t, ht, hu⟩
    refine ⟨fun _ => t, ht, fun b hb => ?_⟩
    rw [e b] at hb ⊢
    rw [hu _ hb]

/-- `1 ≤ codeValue t` on a single nonzero code. -/
def oneLeFormula : GammaOrderLogic.Formula Unit 1 := .ex (.and (.unary () 0) (.not (.lt 1 0)))

theorem oneLe_definable :
    DefinableOverBase B (fun _ : Fin 1 => .rv) {z : Fin 1 → M | Proper z ∧ 1 ≤ codeValue (z 0)} := by
  have h := GammaOrderLogic.formula_definable_base B (fun _ : Unit => ({1} : Set (Values.Gamma (M := M))))
    (fun _ => GammaGroupNames.one_definable_base B) oneLeFormula
  unfold GammaOrderLogic.GammaDefinable at h
  convert h using 3 with z
  simp only [oneLeFormula, GammaOrderLogic.Formula.Realize, Fin.cons_zero, Fin.cons_one,
    Set.mem_singleton_iff, exists_eq_left, not_lt, Set.mem_setOf_eq]

theorem valid_apUnique_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧ ∀ u : Fin D.chart.arity → M,
      Fin.append z u ∈ D.chart.domain → Fin.append z u ∈ {w | ∃! b : Fin 1 → M, Fin.append w b ∈ D.aperture}} :=
  gamma_family_row_subset_definable sp (rvs D.chart.arity) D.chart.domain_definable
    (gamma_family_row_unique_definable (Fin.append sp (rvs D.chart.arity)) (rvs 1) D.aperture_definable)

theorem valid_apDom_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ (u : Fin D.chart.arity → M) (y : Fin 1 → M), Fin.append (Fin.append z u) y ∈ D.aperture →
        Fin.append (Fin.append z u) y ∈ {w | w ∘ Fin.castAdd 1 ∈ D.chart.domain ∧
          w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs 1))}} :=
  row2_forall_definable sp (rvs D.chart.arity) (rvs 1) D.aperture_definable
    (D.chart.domain_definable.preimage_real _ (Fin.castAdd 1))

theorem valid_apValue_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ (u : Fin D.chart.arity → M) (y : Fin 1 → M), Fin.append (Fin.append z u) y ∈ D.aperture →
        Fin.append (Fin.append z u) y ∈ {w | w ∘ Fin.natAdd (p + D.chart.arity) ∈
          {z : Fin 1 → M | Proper z ∧ 1 ≤ codeValue (z 0)} ∧
          w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs 1))}} :=
  row2_forall_definable sp (rvs D.chart.arity) (rvs 1) D.aperture_definable
    (oneLe_definable.preimage_real _ (Fin.natAdd (p + D.chart.arity)))

/-- Parameters `(z, c)` with `codeValue c` bounding the aperture row at `z`. -/
def apBoundSet : Set (Fin (p + 1) → M) :=
  {w | w ∈ sortedUniverse (Fin.append sp (rvs 1)) ∧ NonzeroRV (w (Fin.natAdd p 0)) ∧
    ∀ (u : Fin D.chart.arity → M) (t : M), D.apRow (w ∘ Fin.castAdd 1) u t → NonzeroRV t →
      codeValue t ≤ codeValue (w (Fin.natAdd p 0))}

/-- The order formula `x ≤ c` on the codes `(c, x)`. -/
def leFormula : GammaOrderLogic.Formula Empty 2 := .not (.lt 0 1)

theorem le_codes_definable :
    DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z : Fin 2 → M | Proper z ∧ codeValue (z 1) ≤ codeValue (z 0)} := by
  have h := GammaOrderLogic.formula_definable_base B (fun e : Empty => nomatch e) (fun e => nomatch e) leFormula
  change DefinableOverBase B (fun _ : Fin 2 => .rv) {z | Proper z ∧ ¬ codeValue (z 0) < codeValue (z 1)} at h
  convert h using 3 with z
  simp only [not_lt]

theorem apBoundSet_definable : DefinableOverBase B (Fin.append sp (rvs 1)) D.apBoundSet := by
  let sw := Fin.append sp (rvs 1)
  let a := D.chart.arity
  let st := Fin.append (Fin.append sw (rvs a)) (rvs 1)
  let ι : Fin ((p + a) + 1) → Fin (((p + 1) + a) + 1) :=
    Fin.append (Fin.append (fun i => Fin.castAdd 1 (Fin.castAdd a (Fin.castAdd 1 i)))
      (fun j => Fin.castAdd 1 (Fin.natAdd (p + 1) j))) (fun _ => Fin.natAdd ((p + 1) + a) 0)
  have hAp : DefinableOverBase B st {v | v ∘ ι ∈ D.aperture ∧ v ∈ sortedUniverse st} :=
    D.aperture_definable.preimage_real st ι
  let cI : Fin (((p + 1) + a) + 1) := Fin.castAdd 1 (Fin.castAdd a (Fin.natAdd p 0))
  let tI : Fin (((p + 1) + a) + 1) := Fin.natAdd ((p + 1) + a) 0
  have hC : DefinableOverBase B st
      ((sortedUniverse st \ {v | v ∘ ![tI] ∈ {z | Proper z} ∧ v ∈ sortedUniverse st}) ∪
        {v | v ∘ ![cI, tI] ∈ {z : Fin 2 → M | Proper z ∧ codeValue (z 1) ≤ codeValue (z 0)} ∧
          v ∈ sortedUniverse st}) :=
    (ChartSchema.proper_set_definable _ _ st _).compl.union (le_codes_definable.preimage_real st _)
  have hRow := row2_forall_definable sw (rvs a) (rvs 1) hAp hC
  have hP := ChartSchema.proper_set_definable (M := M) (B := B) (p + 1) 1 sw (Fin.natAdd p)
  convert hRow.inter hP using 1
  ext w
  simp only [apBoundSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  have hι (u : Fin a → M) (y : Fin 1 → M) :
      Fin.append (Fin.append w u) y ∘ ι = Fin.append (Fin.append (w ∘ Fin.castAdd 1) u) y := by
    funext j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [ι]
    · fin_cases l; simp [ι]
  have hy1 (y : Fin 1 → M) : (fun _ : Fin 1 => y 0) = y := by funext j; fin_cases j; rfl
  constructor
  · rintro ⟨hw, hc0, hall⟩
    refine ⟨⟨hw, fun u y hy => ?_⟩, ?_, hw⟩
    · obtain ⟨hy1', hs⟩ := hy
      rw [hι] at hy1'
      by_cases ht : NonzeroRV (y 0)
      · right
        refine ⟨⟨fun l => ?_, ?_⟩, hs⟩
        · fin_cases l
          · simpa [cI, NonzeroRV] using hc0
          · simpa [tI, NonzeroRV] using ht
        · have := hall u (y 0) (by unfold apRow; rw [hy1]; exact hy1') ht
          simpa [cI, tI] using this
      · left
        refine ⟨hs, fun h => ht ?_⟩
        simpa [tI, NonzeroRV] using h.1 0
    · intro l
      fin_cases l
      simpa [NonzeroRV] using hc0
  · rintro ⟨⟨hw, hall⟩, hPw, -⟩
    refine ⟨hw, by simpa [NonzeroRV] using hPw 0, fun u t ht ht0 => ?_⟩
    have hap : Fin.append (Fin.append (w ∘ Fin.castAdd 1) u) (fun _ : Fin 1 => t) ∈ D.aperture := ht
    have hsrt := mem_rows_sorted sp (rvs a) (rvs 1) D.aperture_definable hap
    have hs : Fin.append (Fin.append w u) (fun _ : Fin 1 => t) ∈ sortedUniverse st :=
      sorted_append (sorted_append (fun i => hw i) hsrt.1) hsrt.2
    rcases hall u (fun _ => t) ⟨by rw [hι]; exact hap, hs⟩ with h | h
    · exact absurd ⟨fun l => by fin_cases l; simpa [tI, NonzeroRV] using ht0, h.1⟩ h.2
    · simpa [cI, tI] using h.1.2

/-- Index map placing `(z, u, update t j s)` inside the layout `(z, t, u, s)`. -/
def inactIndex (p a k : ℕ) (j : Fin (1 + k)) : Fin ((p + a) + (1 + k)) → Fin (((p + (1 + k)) + a) + 1) :=
  Fin.append (Fin.append (fun i => Fin.castAdd 1 (Fin.castAdd a (Fin.castAdd (1 + k) i)))
    (fun i => Fin.castAdd 1 (Fin.natAdd (p + (1 + k)) i)))
    (fun i => if i = j then Fin.natAdd ((p + (1 + k)) + a) 0 else Fin.castAdd 1 (Fin.castAdd a (Fin.natAdd p i)))

omit hM in
theorem append_inactIndex {a : ℕ} (j : Fin (1 + k)) (z : Fin p → M) (t : Fin (1 + k) → M) (u : Fin a → M)
    (s : Fin 1 → M) :
    Fin.append (Fin.append (Fin.append z t) u) s ∘ inactIndex p a k j =
      Fin.append (Fin.append z u) (Function.update t j (s 0)) := by
  funext idx
  refine Fin.addCases (fun l => ?_) (fun i => ?_) idx
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [inactIndex]
  · by_cases hi : i = j
    · subst hi
      simp [inactIndex]
    · simp [inactIndex, hi, Function.update_of_ne hi]

/-- The inactive relation in the layout `(z, t, u)`. -/
def inactSet : Set (Fin ((p + (1 + k)) + D.chart.arity) → M) :=
  {w | ∃ s : Fin 1 → M, Fin.append w s ∈ {v | v ∘ inactIndex p D.chart.arity k D.coordinate ∈ D.chart.coord ∧
    v ∈ sortedUniverse (Fin.append (Fin.append (Fin.append sp (rvs (1 + k))) (rvs D.chart.arity)) (rvs 1))}}

theorem inactSet_definable :
    DefinableOverBase B (Fin.append (Fin.append sp (rvs (1 + k))) (rvs D.chart.arity)) D.inactSet :=
  gamma_family_row_exists_definable _ (rvs 1) (D.chart.coord_definable.preimage_real _ _)

theorem mem_inactSet_iff {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) {t : Fin (1 + k) → M}
    (ht : ∀ i, sortEval SortTag.rv (t i)) (u : Fin D.chart.arity → M) :
    Fin.append (Fin.append z t) u ∈ D.inactSet ↔ D.inactRel z u t := by
  constructor
  · rintro ⟨s, h, -⟩
    rw [append_inactIndex] at h
    exact ⟨s 0, h⟩
  · rintro ⟨s, h⟩
    have hsrt := mem_rows_sorted sp (rvs D.chart.arity) (rvs (1 + k)) D.chart.coord_definable h
    have hs : sortEval SortTag.rv s := by
      have := hsrt.2 D.coordinate
      simpa using this
    refine ⟨fun _ => s, ?_, ?_⟩
    · show _ ∈ D.chart.coord
      rw [append_inactIndex]
      exact h
    · exact sorted_append (sorted_append (sorted_append hz ht) hsrt.1) (fun _ => hs)

theorem valid_inactive_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧ ∀ t : Fin (1 + k) → M,
      (∀ j, sortEval (rvs (1 + k) j) (t j)) → Fin.append z t ∈
        {w | (∀ i, sortEval (Fin.append sp (rvs (1 + k)) i) (w i)) ∧
          {u : Fin D.chart.arity → M | Fin.append w u ∈ D.inactSet}.Finite ∧
          {u : Fin D.chart.arity → M | Fin.append w u ∈ D.inactSet}.ncard ≤ D.inactiveBound}} :=
  gamma_family_row_forall_definable sp (rvs (1 + k))
    (gamma_family_finite_bound_definable _ (rvs D.chart.arity) D.inactiveBound D.inactSet_definable)

/-- **The validity locus of a datum schema is `B`-definable.** -/
theorem valid_definable : DefinableOverBase B sp {z | D.Valid z} := by
  have h := D.chart.valid_definable.inter (D.valid_apUnique_definable.inter (D.valid_apDom_definable.inter
    (D.valid_apValue_definable.inter ((gamma_family_row_exists_definable sp (rvs 1) D.apBoundSet_definable).inter
      D.valid_inactive_definable))))
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  have hy1 (y : Fin 1 → M) : (fun _ : Fin 1 => y 0) = y := by funext j; fin_cases j; rfl
  constructor
  · intro hz
    have hs := hz.chart.sorted
    refine ⟨hz.chart, ⟨hs, fun u hu => ?_⟩, ⟨hs, fun u y hy => ?_⟩, ⟨hs, fun u y hy => ?_⟩, ?_, ⟨hs, fun t ht => ?_⟩⟩
    · show ∃! b : Fin 1 → M, Fin.append (Fin.append z u) b ∈ D.aperture
      rw [existsUnique_fin_one]
      exact hz.ap_unique u hu
    · have hap : D.apRow z u (y 0) := by unfold apRow; rw [hy1]; exact hy
      refine ⟨?_, D.aperture_definable.proper _ hy⟩
      rw [ChartSchema.append_comp_castAdd]
      exact hz.ap_dom u _ hap
    · have hap : D.apRow z u (y 0) := by unfold apRow; rw [hy1]; exact hy
      obtain ⟨h0, h1⟩ := hz.ap_value u _ hap
      refine ⟨?_, D.aperture_definable.proper _ hy⟩
      rw [ChartSchema.append_comp_natAdd]
      exact ⟨fun l => by fin_cases l; exact h0, h1⟩
    · obtain ⟨Δ, hΔ⟩ := hz.ap_bounded
      refine ⟨fun _ => GammaParameters.raw (GammaParameters.representative Δ), ?_, ?_, ?_⟩
      · exact sorted_append hs (fun _ => (ChartSchema.nonzero_raw _).1)
      · simpa [NonzeroRV] using ChartSchema.nonzero_raw (GammaParameters.representative Δ)
      · intro u t ht ht0
        rw [ChartSchema.append_comp_castAdd] at ht
        simpa [ChartSchema.codeValue_raw_representative] using hΔ u t ht
    · have hrel := hz.inactive t ht
      refine ⟨sorted_append hs ht, ?_⟩
      have he : {u : Fin D.chart.arity → M | Fin.append (Fin.append z t) u ∈ D.inactSet} = {u | D.inactRel z u t} :=
        Set.ext (fun u => D.mem_inactSet_iff hs ht u)
      rw [he]
      exact hrel
  · rintro ⟨hc, ⟨hs, hU⟩, ⟨-, hD⟩, ⟨-, hV⟩, ⟨b, hb⟩, ⟨-, hI⟩⟩
    have hval : ∀ u t, D.apRow z u t → NonzeroRV t ∧ 1 ≤ codeValue t := by
      intro u t ht
      have := (hV u (fun _ => t) ht).1
      rw [ChartSchema.append_comp_natAdd] at this
      exact ⟨this.1 0, this.2⟩
    refine ⟨hc, fun u hu => ?_, fun u t ht => ?_, hval, ?_, fun t ht => ?_⟩
    · have : ∃! b : Fin 1 → M, Fin.append (Fin.append z u) b ∈ D.aperture := hU u hu
      rw [existsUnique_fin_one] at this
      exact this
    · have := (hD u (fun _ => t) ht).1
      rw [ChartSchema.append_comp_castAdd] at this
      exact this
    · obtain ⟨-, -, hall⟩ := hb
      refine ⟨codeValue (b 0), fun u t ht => ?_⟩
      have ht' : D.apRow (Fin.append z b ∘ Fin.castAdd 1) u t := by rw [ChartSchema.append_comp_castAdd]; exact ht
      simpa using hall u t ht' (hval u t ht).1
    · have := (hI t ht).2
      have he : {u : Fin D.chart.arity → M | Fin.append (Fin.append z t) u ∈ D.inactSet} = {u | D.inactRel z u t} :=
        Set.ext (fun u => D.mem_inactSet_iff hs ht u)
      rw [he] at this
      exact this

end DatumDefinable

end DatumSchema

end DiamondIntegral.Section7.Lemma714Schema
