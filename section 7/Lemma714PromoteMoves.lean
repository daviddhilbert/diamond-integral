import «section 7».Lemma714Promote

/-! Lemma 7.14, part 7: promotion of aperture data and of explicit moves.

The point `z` and the base `C` (in the application `S⟨a⟩`) satisfy
`Promotable B C z` and `B ∪ z ⊆ C`. A schema valid at `z` then has a chart over
`C` (`extChart`, by base extension), and a promoted chart is identified with
its source chart by the identity map (`promoteChart_iso`). An aperture datum
over `C` is the row at `z` of a valid datum schema (`promoteDatum`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks AnnularBlowup BlowupChart RelativeAnnularGenerators
open IntegrationInACVF.Section6
open DiamondIntegral.Section7.BoundedClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

section Ext
variable {C : Base (M := M)} {z : Fin p → M} (hr : (baseAt B z).real ⊆ C.real) (hg : (baseAt B z).gamma ⊆ C.gamma)
variable {d : ℕ}

/-- The chart of a valid row, over the larger base `C`. -/
def extChart (W : ChartSchema B sp d) (hW : W.Valid z) : Chart C d :=
  BaseExtension.chartExt hr hg (W.toChart z hW)

/-- The bounded object of a valid row, over `C`. -/
def extObj (W : ChartSchema B sp d) (hW : W.Valid z) : Obj C d :=
  ⟨extChart hr hg W hW, ChartSchema.toChart_domainBounded hW⟩

theorem extChart_weight (W : ChartSchema B sp d) (hW : W.Valid z) (u : Fin W.arity → M) :
    (extChart hr hg W hW).correctedWeight u = W.weightAt z u := rfl

variable (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)

/-- A promoted chart is identified with its source by the identity map. -/
def promoteChart_iso (c : Chart C d) (N : ℕ) (hW : (promoteChart hz hC c N).Valid z) :
    Iso c (extChart hr hg (promoteChart hz hC c N) hW) :=
  isoOfMap c _ (fun u => u)
    (by
      have h := RVCoordinateMaps.coordinate_graph_definable C c.domain c.domain_definable (id : Fin c.arity → Fin c.arity)
      exact h)
    (by
      have hrow : (extChart hr hg (promoteChart hz hC c N) hW).domain = c.domain := promoteChart_row hz hC c N
      rw [hrow]
      exact Set.bijOn_id c.domain)
    (fun u hu => by
      rw [extChart_weight, promoteChart_weightAt hz hC c N hW u hu])

end Ext

/-! ### Promoting aperture data -/

section PromoteDatum
variable {C : Base (M := M)} {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)
  {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk (baseAt B z).real < κ)
  (hgamma : Cardinal.mk (baseAt B z).gamma < κ) {k : ℕ}

/-- The aperture graph in the append layout `(u, τ(u))`. -/
def apSet (D : AnnularDatum C k) : Set (Fin (D.chart.arity + 1) → M) :=
  {w | (fun i => w (Fin.castAdd 1 i)) ∈ D.chart.domain ∧
    (fun _ : Fin 1 => D.aperture.aperture (fun i => w (Fin.castAdd 1 i))) = fun j => w (Fin.natAdd D.chart.arity j)}

theorem apSet_definable (D : AnnularDatum C k) :
    DefinableOverBase C (Fin.append (rvs D.chart.arity) (rvs 1)) (apSet D) := by
  have h := append_graph_definable D.chart.domain (fun u => ![D.aperture.aperture u])
    (fun u hu i => D.chart.domain_definable.proper u hu i)
    (fun u hu i => by fin_cases i; exact (D.aperture.nonzero u hu).1) D.aperture.graph_definable
  convert h using 1
  ext w
  simp only [apSet, Set.mem_setOf_eq]
  have e : (fun _ : Fin 1 => D.aperture.aperture (fun i => w (Fin.castAdd 1 i))) =
      ![D.aperture.aperture (fun i => w (Fin.castAdd 1 i))] := by
    funext j; fin_cases j; rfl
  rw [e]

/-- The datum schema before the inactive bound is chosen. -/
def promoteDatum0 (D : AnnularDatum C k) : DatumSchema B sp k where
  chart := promoteObj hz hC hκ hs hreal hgamma D.source
  coordinate := D.coordinate
  aperture := (promoteSet2 hz hC (rvs D.chart.arity) (rvs 1) (apSet D) (apSet_definable D)).choose
  aperture_definable := (promoteSet2 hz hC (rvs D.chart.arity) (rvs 1) (apSet D) (apSet_definable D)).choose_spec.1
  inactiveBound := 0

variable (D : AnnularDatum C k)

theorem promoteDatum0_row : (promoteDatum0 hz hC hκ hs hreal hgamma D).chart.row z = D.chart.domain :=
  promoteChart_row hz hC D.chart _

theorem promoteDatum0_coordRow (u : Fin D.chart.arity → M) (y : Fin (1 + k) → M) :
    (promoteDatum0 hz hC hκ hs hreal hgamma D).chart.coordRow z u y ↔ u ∈ D.chart.domain ∧ D.chart.coordinate u = y :=
  promoteChart_coordRow hz hC D.chart _ u y

theorem promoteDatum0_apRow (u : Fin D.chart.arity → M) (t : M) :
    (promoteDatum0 hz hC hκ hs hreal hgamma D).apRow z u t ↔ u ∈ D.chart.domain ∧ D.aperture.aperture u = t := by
  have h := (promoteSet2 hz hC (rvs D.chart.arity) (rvs 1) (apSet D) (apSet_definable D)).choose_spec.2 u
    (fun _ => t)
  change _ ∈ (promoteSet2 hz hC (rvs D.chart.arity) (rvs 1) (apSet D) (apSet_definable D)).choose ↔ _
  rw [h]
  simp only [apSet, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨hu, he⟩
    exact ⟨hu, congrFun he 0⟩
  · rintro ⟨hu, he⟩
    exact ⟨hu, by funext j; exact he⟩

theorem promoteDatum0_inactRel (u : Fin D.chart.arity → M) (t : Fin (1 + k) → M) :
    (promoteDatum0 hz hC hκ hs hreal hgamma D).inactRel z u t ↔
      ∃ s, u ∈ D.chart.domain ∧ D.chart.coordinate u = Function.update t D.coordinate s := by
  unfold DatumSchema.inactRel
  simp only [promoteDatum0_coordRow]
  rfl

theorem promoteDatum0_inactive_finite (t : Fin (1 + k) → M) :
    {u | (promoteDatum0 hz hC hκ hs hreal hgamma D).inactRel z u t}.Finite := by
  apply (D.finite (Function.update t D.coordinate iRVOne)).subset
  intro u hu
  obtain ⟨s, hu, he⟩ := (promoteDatum0_inactRel hz hC hκ hs hreal hgamma D u t).mp hu
  refine ⟨hu, ?_⟩
  simp only [inactive, he, Function.update_idem]

theorem inactSet_row_sorted {t : Fin (1 + k) → M} {u : Fin D.chart.arity → M}
    (h : Fin.append (Fin.append z t) u ∈ (promoteDatum0 hz hC hκ hs hreal hgamma D).inactSet) :
    ∀ i, sortEval SortTag.rv (t i) := by
  obtain ⟨s, -, hs'⟩ := h
  intro i
  have := hs' (Fin.castAdd 1 (Fin.castAdd D.chart.arity (Fin.natAdd p i)))
  simp only [Fin.append_left, Fin.append_right] at this
  change sortEval (Fin.append (Fin.append sp (rvs (1 + k))) (rvs D.chart.arity)
    (Fin.castAdd D.chart.arity (Fin.natAdd p i))) (t i) at this
  simpa using this

theorem exists_inactive_bound :
    ∃ N : ℕ, ∀ t : Fin (1 + k) → M, (∀ i, sortEval SortTag.rv (t i)) →
      {u | (promoteDatum0 hz hC hκ hs hreal hgamma D).inactRel z u t}.ncard ≤ N := by
  let D0 := promoteDatum0 hz hC hκ hs hreal hgamma D
  have hrow := row2_definable sp (rvs (1 + k)) (rvs D.chart.arity) D0.inactSet_definable z
  have hself : Promotable B (baseAt B z) z := fun _ _ h => h
  have hrowset : ∀ (t : Fin (1 + k) → M), {u : Fin D.chart.arity → M | Fin.append t u ∈
      {w : Fin ((1 + k) + D.chart.arity) → M | Fin.append (Fin.append z (fun i => w (Fin.castAdd D.chart.arity i)))
        (fun j => w (Fin.natAdd (1 + k) j)) ∈ D0.inactSet}} =
      {u | Fin.append (Fin.append z t) u ∈ D0.inactSet} := by
    intro t
    ext u
    simp only [Set.mem_setOf_eq, Fin.append_left, Fin.append_right]
    exact Iff.rfl
  obtain ⟨N, hN⟩ := exists_uniform_bound hself hκ hs hreal hgamma (rvs (1 + k)) (rvs D.chart.arity) _ hrow (by
    intro t
    rw [hrowset]
    by_cases ht : ∀ i, sortEval SortTag.rv (t i)
    · have he : {u | Fin.append (Fin.append z t) u ∈ D0.inactSet} = {u | D0.inactRel z u t} :=
        Set.ext (fun u => D0.mem_inactSet_iff hz ht u)
      rw [he]
      exact promoteDatum0_inactive_finite hz hC hκ hs hreal hgamma D t
    · refine Set.Finite.subset Set.finite_empty ?_
      intro u hu
      exact (ht (inactSet_row_sorted hz hC hκ hs hreal hgamma D hu)).elim)
  refine ⟨N, fun t ht => ?_⟩
  have he : {u | D0.inactRel z u t} = {u | Fin.append (Fin.append z t) u ∈ D0.inactSet} :=
    Set.ext (fun u => (D0.mem_inactSet_iff hz ht u).symm)
  rw [he, ← hrowset]
  exact hN t ht

/-- **Promotion of an aperture datum** over `C` to a datum schema over `B` with
row `D` at `z`. -/
def promoteDatum : DatumSchema B sp k :=
  { promoteDatum0 hz hC hκ hs hreal hgamma D with
    inactiveBound := (exists_inactive_bound hz hC hκ hs hreal hgamma D).choose }

theorem promoteDatum_valid : (promoteDatum hz hC hκ hs hreal hgamma D).Valid z := by
  have hc := promoteObj_valid (sp := sp) hz hC hκ hs hreal hgamma D.source
  refine ⟨hc, fun u hu => ?_, fun u t h => ?_, fun u t h => ?_, ⟨D.aperture.bound, fun u t h => ?_⟩, fun t ht => ?_⟩
  · have hu' : u ∈ D.chart.domain := by rw [← promoteDatum0_row hz hC hκ hs hreal hgamma D]; exact hu
    exact ⟨_, (promoteDatum0_apRow hz hC hκ hs hreal hgamma D u _).mpr ⟨hu', rfl⟩,
      fun t h => ((promoteDatum0_apRow hz hC hκ hs hreal hgamma D u t).mp h).2.symm⟩
  · have := ((promoteDatum0_apRow hz hC hκ hs hreal hgamma D u t).mp h).1
    rw [← promoteDatum0_row hz hC hκ hs hreal hgamma D] at this
    exact this
  · obtain ⟨hu, rfl⟩ := (promoteDatum0_apRow hz hC hκ hs hreal hgamma D u t).mp h
    exact ⟨D.aperture.nonzero u hu, D.aperture.nonnegative u hu⟩
  · obtain ⟨hu, rfl⟩ := (promoteDatum0_apRow hz hC hκ hs hreal hgamma D u t).mp h
    exact D.aperture.bounded u hu
  · exact ⟨promoteDatum0_inactive_finite hz hC hκ hs hreal hgamma D t,
      (exists_inactive_bound hz hC hκ hs hreal hgamma D).choose_spec t ht⟩

end PromoteDatum

/-! ### Weights of restrictions -/

namespace ChartSchema
variable {d : ℕ} {W : ChartSchema B sp d} {P : Set (Fin (p + W.arity) → M)}
  {hP : DefinableOverBase B (Fin.append sp (rvs W.arity)) P} {z : Fin p → M}

theorem restrict_weightAt (hW : W.Valid z) {u : Fin W.arity → M} (hu : u ∈ (W.restrict P hP).row z) :
    (W.restrict P hP).weightAt z u = W.weightAt z u := by
  have hR := hW.restrict (P := P) (hP := hP)
  have h1 := coordRow_coordAt hR hu
  rw [restrict_coordRow] at h1
  have hco : (W.restrict P hP).coordAt z u = W.coordAt z u :=
    ((coordRow_iff hW u _).mp h1.1).2.symm
  obtain ⟨c, hc⟩ := hR.vol_total u hu
  have hv1 := ((volRow_iff hR u c).mp hc).2.2
  have hc' := ((restrict_volRow z u c).mp hc).1
  have hv2 := ((volRow_iff hW u c).mp hc').2.2
  unfold weightAt
  rw [hco, ← hv1, hv2]

end ChartSchema

/-! ### Row maps -/

section RowMaps
variable {C : Base (M := M)}

/-- A `C`-definable bijection between two sets of rows that preserves the
given weights. -/
structure RowMap {a b : ℕ} (I : Set (Fin a → M)) (J : Set (Fin b → M))
    (wa : (Fin a → M) → Values.Gamma (M := M)) (wb : (Fin b → M) → Values.Gamma (M := M)) where
  F : (Fin a → M) → (Fin b → M)
  graph : DefinableOverBase C (fun _ : Fin (b + a) => .rv) (graphOn I F)
  bij : Set.BijOn F I J
  weight : ∀ u ∈ I, wa u = wb (F u)

namespace RowMap
variable {a b c : ℕ} {I : Set (Fin a → M)} {J : Set (Fin b → M)} {K : Set (Fin c → M)}
  {wa : (Fin a → M) → Values.Gamma (M := M)} {wb : (Fin b → M) → Values.Gamma (M := M)}
  {wc : (Fin c → M) → Values.Gamma (M := M)}

/-- Composition of row maps. -/
def comp (G : RowMap (C := C) J K wb wc) (F : RowMap (C := C) I J wa wb) : RowMap (C := C) I K wa wc where
  F := G.F ∘ F.F
  graph := RVGraphComposition.graph_compose_definable C I J F.F G.F F.graph G.graph F.bij.mapsTo
  bij := G.bij.comp F.bij
  weight := fun u hu => (F.weight u hu).trans (G.weight _ (F.bij.mapsTo hu))

/-- Changing the weight functions on the source and target. -/
def congrWeight (F : RowMap (C := C) I J wa wb) {wa' : (Fin a → M) → Values.Gamma (M := M)}
    {wb' : (Fin b → M) → Values.Gamma (M := M)} (ha : ∀ u ∈ I, wa' u = wa u) (hb : ∀ v ∈ J, wb v = wb' v) :
    RowMap (C := C) I J wa' wb' where
  F := F.F
  graph := F.graph
  bij := F.bij
  weight := fun u hu => (ha u hu).trans ((F.weight u hu).trans (hb _ (F.bij.mapsTo hu)))

/-- Changing the source and target sets along equalities. -/
def congrSets (F : RowMap (C := C) I J wa wb) {I' : Set (Fin a → M)} {J' : Set (Fin b → M)}
    (hI : I' = I) (hJ : J' = J) : RowMap (C := C) I' J' wa wb := by
  subst hI hJ
  exact F

end RowMap

/-- A measured isomorphism over `C`, restricted to a piece mapped onto a piece. -/
def RowMap.ofIso {k : ℕ} {x y : Chart C k} (G : Iso x y) (I : Set (Fin x.arity → M)) (J : Set (Fin y.arity → M))
    (hI : I ⊆ x.domain) (hIdef : DefinableOverBase C (fun _ : Fin x.arity => .rv) I)
    (hIJ : Set.BijOn (isoMap G) I J) :
    RowMap (C := C) I J x.correctedWeight y.correctedWeight where
  F := isoMap G
  graph := by
    have h := graph_inter_definable x.domain I (isoMap G) (isoMap_graph G) hIdef
    rwa [Set.inter_eq_self_of_subset_right hI] at h
  bij := hIJ
  weight := fun u hu => isoMap_weight G u (hI hu)

variable {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)

include hz hC in
/-- A row map between the valid rows of two schemata gives a valid isomorphism
schema. -/
theorem RowMap.exists_isoSchema {d : ℕ} {X Y : ChartSchema B sp d} (hX : X.Valid z) (hY : Y.Valid z)
    (F : RowMap (C := C) (X.row z) (Y.row z) (X.weightAt z) (Y.weightAt z)) :
    ∃ Φ : IsoSchema X Y, Φ.Valid z := by
  refine Lemma714Schema.exists_isoSchema hz hC hX hY F.F ?_ F.bij F.weight
  exact append_graph_definable (X.row z) F.F (fun u hu i => ChartSchema.row_rv hu i)
    (fun u hu i => ChartSchema.row_rv (F.bij.mapsTo hu) i) F.graph

end RowMaps

/-! ### Pieces of coproducts and preimages -/

section Pieces
variable {C : Base (M := M)} {k : ℕ}
open RVChartDisjointUnion RVChartRestrictions RVTaggedCoproduct

/-- The preimage of a definable piece of the target under a measured isomorphism. -/
def prePiece {x y : Chart C k} (G : Iso x y) (J : Set (Fin y.arity → M)) : Set (Fin x.arity → M) :=
  x.domain ∩ {u | isoMap G u ∈ J}

theorem prePiece_definable {x y : Chart C k} (G : Iso x y) (J : Set (Fin y.arity → M))
    (hJ : DefinableOverBase C (fun _ : Fin y.arity => .rv) J) :
    DefinableOverBase C (fun _ : Fin x.arity => .rv) (prePiece G J) := by
  have h0 := ((isoMap_graph G).inter (hJ.preimage_real (fun _ : Fin (y.arity + x.arity) => .rv)
    (tailIndex y.arity x.arity))).image_real (headIndex y.arity x.arity)
  have h : DefinableOverBase C (fun _ : Fin x.arity => .rv) _ := h0
  convert h using 1
  ext u
  constructor
  · rintro ⟨hu, hJu⟩
    refine ⟨join y.arity x.arity u (isoMap G u), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [join_comp_head]; exact hu
    · rw [join_comp_head, join_comp_tail]
    · rw [join_comp_tail]; exact hJu
    · apply GammaBoundedProducts.all_coordinates y.arity x.arity (fun x => sortEval SortTag.rv x)
      · intro i; rw [join_head]; exact x.domain_definable.proper u hu i
      · intro i; rw [join_tail]; exact y.domain_definable.proper _ ((isoMap_bijOn G).1 hu) i
    · exact join_comp_head _ _
  · rintro ⟨w, ⟨⟨hw1, hw2⟩, hJw, -⟩, rfl⟩
    refine ⟨hw1, ?_⟩
    change isoMap G (w ∘ headIndex y.arity x.arity) ∈ J
    rw [hw2]
    exact hJw

theorem prePiece_bijOn {x y : Chart C k} (G : Iso x y) (J : Set (Fin y.arity → M)) :
    Set.BijOn (isoMap G) (prePiece G J) (y.domain ∩ J) := by
  refine ⟨fun u hu => ⟨(isoMap_bijOn G).1 hu.1, hu.2⟩, (isoMap_bijOn G).2.1.mono (fun u hu => hu.1), ?_⟩
  rintro v ⟨hv, hJv⟩
  obtain ⟨u, hu, rfl⟩ := (isoMap_bijOn G).2.2 hv
  exact ⟨u, ⟨hu, hJv⟩, rfl⟩

theorem prePiece_compl_bijOn {x y : Chart C k} (G : Iso x y) (J : Set (Fin y.arity → M)) :
    Set.BijOn (isoMap G) (x.domain \ prePiece G J) (y.domain \ J) := by
  refine ⟨fun u hu => ⟨(isoMap_bijOn G).1 hu.1, fun h => hu.2 ⟨hu.1, h⟩⟩,
    (isoMap_bijOn G).2.1.mono (fun u hu => hu.1), ?_⟩
  rintro v ⟨hv, hJv⟩
  obtain ⟨u, hu, rfl⟩ := (isoMap_bijOn G).2.2 hv
  exact ⟨u, ⟨hu, fun h => hJv h.2⟩, rfl⟩

theorem coprodInsideLeft_bijOn (a b : Chart C k) :
    Set.BijOn (isoMap (coprodInsideLeft a b)) ((coproduct a b).domain ∩ (L a b).domain) a.domain :=
  isoMap_bijOn (coprodInsideLeft a b)

theorem coprodOutsideLeft_bijOn (a b : Chart C k) :
    Set.BijOn (isoMap (coprodOutsideLeft a b)) ((coproduct a b).domain \ (L a b).domain) b.domain :=
  isoMap_bijOn (coprodOutsideLeft a b)

theorem coprodInsideRight_bijOn (a b : Chart C k) :
    Set.BijOn (isoMap (coprodInsideRight a b)) ((coproduct a b).domain ∩ (R a b).domain) b.domain :=
  isoMap_bijOn (coprodInsideRight a b)

end Pieces

/-! ### Facts about promoted data -/

section PromoteDatumFacts
variable {C : Base (M := M)} {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)
  {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk (baseAt B z).real < κ)
  (hgamma : Cardinal.mk (baseAt B z).gamma < κ) {k : ℕ} (D : AnnularDatum C k)

theorem promoteDatum_row : (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z = D.chart.domain :=
  promoteDatum0_row hz hC hκ hs hreal hgamma D

theorem promoteDatum_coordAt {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    (promoteDatum hz hC hκ hs hreal hgamma D).chart.coordAt z u = D.chart.coordinate u := by
  have hv := (promoteDatum_valid hz hC hκ hs hreal hgamma D).chart
  have hu' : u ∈ (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z := by
    rw [promoteDatum_row]; exact hu
  exact ((promoteDatum0_coordRow hz hC hκ hs hreal hgamma D u _).mp (ChartSchema.coordRow_coordAt hv hu')).2.symm

theorem promoteDatum_volAt {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    (promoteDatum hz hC hκ hs hreal hgamma D).chart.volAt z u = D.chart.volume u := by
  have hv := (promoteDatum_valid hz hC hκ hs hreal hgamma D).chart
  have hu' : u ∈ (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z := by
    rw [promoteDatum_row]; exact hu
  obtain ⟨c, hc⟩ := hv.vol_total u hu'
  rw [← ((ChartSchema.volRow_iff hv u c).mp hc).2.2]
  exact ((promoteChart_volRow hz hC D.chart _ u c).mp hc).2.2

theorem promoteDatum_apRow (u : Fin D.chart.arity → M) (t : M) :
    (promoteDatum hz hC hκ hs hreal hgamma D).apRow z u t ↔ u ∈ D.chart.domain ∧ D.aperture.aperture u = t :=
  promoteDatum0_apRow hz hC hκ hs hreal hgamma D u t

end PromoteDatumFacts

/-! ### Canonical row maps for the endpoint and the shell -/

namespace DatumSchema
variable {k : ℕ} {D : DatumSchema B sp k} {z : Fin p → M}

theorem endSchema_coordAt (hD : D.Valid z) {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.row z) :
    D.endSchema.coordAt z u =
      Function.update (D.chart.coordAt z u) D.coordinate (iRVMul (D.apAt z u) (D.chart.coordAt z u D.coordinate)) :=
  ((ChartSchema.coordRow_iff hD.endSchema u _).mp ((endSchema_coordRow_iff hD u _).mpr ⟨hu, rfl⟩)).2

theorem endSchema_volAt (u : Fin D.chart.arity → M) : D.endSchema.volAt z u = D.chart.volAt z u := rfl

theorem shellSchema_coordAt (hD : D.Valid z) {u : Fin D.chart.arity → M} {s0 : M}
    (hus : Fin.append u (fun _ : Fin 1 => s0) ∈ D.shellSchema.row z) :
    D.shellSchema.coordAt z (Fin.append u (fun _ : Fin 1 => s0)) =
      Function.update (D.chart.coordAt z u) D.coordinate (iRVMul s0 (D.chart.coordAt z u D.coordinate)) :=
  ((ChartSchema.coordRow_iff hD.shellSchema _ _).mp ((shell_coordRow_iff hD u s0 _).mpr ⟨hus, rfl⟩)).2

theorem shellSchema_volAt (hD : D.Valid z) {u : Fin D.chart.arity → M} {s0 : M}
    (hus : Fin.append u (fun _ : Fin 1 => s0) ∈ D.shellSchema.row z) :
    D.shellSchema.volAt z (Fin.append u (fun _ : Fin 1 => s0)) = D.chart.volAt z u := by
  have hv := hD.shellSchema
  obtain ⟨c, hc⟩ := hv.vol_total _ hus
  rw [← ((ChartSchema.volRow_iff hv _ c).mp hc).2.2]
  have h2 := ((D.shell_volRow z u s0 c).mp hc).2
  exact ((ChartSchema.volRow_iff hD.chart u c).mp h2).2.2

end DatumSchema

section Canon
variable {C : Base (M := M)} {z : Fin p → M} (hz : ∀ i, sortEval (sp i) (z i)) (hC : Promotable B C z)
  {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk (baseAt B z).real < κ)
  (hgamma : Cardinal.mk (baseAt B z).gamma < κ) {k : ℕ} (D : AnnularDatum C k)

theorem promoteDatum_apAt {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    (promoteDatum hz hC hκ hs hreal hgamma D).apAt z u = D.aperture.aperture u := by
  have hv := promoteDatum_valid hz hC hκ hs hreal hgamma D
  have hu' : u ∈ (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z := by
    rw [promoteDatum_row]; exact hu
  exact ((promoteDatum_apRow hz hC hκ hs hreal hgamma D u _).mp (DatumSchema.apRow_apAt hv hu')).2.symm

/-- The endpoint of Section 4 as rows of the endpoint schema: `(u, τ(u)) ↦ u`. -/
def endCanon : RowMap (C := C) (endpointChart D.chart D.coordinate D.finite D.aperture).domain
    ((promoteDatum hz hC hκ hs hreal hgamma D).endSchema.row z)
    (endpointChart D.chart D.coordinate D.finite D.aperture).correctedWeight
    ((promoteDatum hz hC hκ hs hreal hgamma D).endSchema.weightAt z) where
  F := fun w => w ∘ headIndex 1 D.chart.arity
  graph := RVCoordinateMaps.coordinate_graph_definable C _
    (endpointChart D.chart D.coordinate D.finite D.aperture).domain_definable (headIndex 1 D.chart.arity)
  bij := by
    have hrow : (promoteDatum hz hC hκ hs hreal hgamma D).endSchema.row z = D.chart.domain :=
      promoteDatum_row hz hC hκ hs hreal hgamma D
    rw [hrow]
    refine ⟨fun w hw => hw.1, fun w hw w' hw' he => ?_, fun u hu => ?_⟩
    · rw [graph_canonical D.chart D.aperture hw, graph_canonical D.chart D.aperture hw']
      simp only at he
      rw [he]
    · refine ⟨join 1 D.chart.arity u ![D.aperture.aperture u], ⟨?_, ?_⟩, join_comp_head _ _⟩
      · rw [join_comp_head]; exact hu
      · rw [join_comp_head, join_comp_tail]
  weight := by
    intro w hw
    have hu : w ∘ headIndex 1 D.chart.arity ∈ D.chart.domain := hw.1
    have hv := promoteDatum_valid hz hC hκ hs hreal hgamma D
    have hu' : w ∘ headIndex 1 D.chart.arity ∈ (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z := by
      rw [promoteDatum_row]; exact hu
    show D.chart.volume (w ∘ headIndex 1 D.chart.arity) * ∏ l, codeValue (blownCoordinate D.chart D.coordinate
      (w ∘ headIndex 1 D.chart.arity) (w (aIdx D.chart)) l) = _
    unfold ChartSchema.weightAt
    rw [DatumSchema.endSchema_volAt, DatumSchema.endSchema_coordAt hv hu', promoteDatum_volAt hz hC hκ hs hreal hgamma D hu,
      promoteDatum_coordAt hz hC hκ hs hreal hgamma D hu, promoteDatum_apAt hz hC hκ hs hreal hgamma D hu,
      graph_aperture D.chart D.aperture hw]
    rfl

/-- Index map reading `(u, s)` off a Section 4 shell point. -/
def shellIdx {k : ℕ} {C : Base (M := M)} (r : Chart C k) : Fin (r.arity + 1) → Fin (1 + (1 + r.arity)) :=
  Fin.append (xIdx r) (fun _ => sIdx r)

theorem comp_shellIdx {k : ℕ} {C : Base (M := M)} (r : Chart C k) (w : Fin (1 + (1 + r.arity)) → M) :
    w ∘ shellIdx r = Fin.append (w ∘ xIdx r) (fun _ : Fin 1 => w (sIdx r)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [shellIdx]

theorem shell_mapsTo {w : Fin (1 + (1 + D.chart.arity)) → M}
    (hw : w ∈ (shellChart D.chart D.coordinate D.finite D.aperture).domain) :
    Fin.append (w ∘ xIdx D.chart) (fun _ : Fin 1 => w (sIdx D.chart)) ∈
      (promoteDatum hz hC hκ hs hreal hgamma D).shellSchema.row z := by
  have hrowD : (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z = D.chart.domain :=
    promoteDatum_row hz hC hκ hs hreal hgamma D
  obtain ⟨hu, hs0, h1, hle⟩ := shell_points D.chart D.aperture hw
  change Fin.append z _ ∈ (promoteDatum hz hC hκ hs hreal hgamma D).shellDom
  rw [DatumSchema.mem_shellDom]
  refine ⟨?_, hs0, h1, D.aperture.aperture (w ∘ xIdx D.chart),
    (promoteDatum_apRow hz hC hκ hs hreal hgamma D _ _).mpr ⟨hu, rfl⟩, hle⟩
  change w ∘ xIdx D.chart ∈ (promoteDatum hz hC hκ hs hreal hgamma D).chart.row z
  rw [hrowD]
  exact hu

/-- The shell of Section 4 as rows of the shell schema: `w ↦ (u, s)`. -/
def shellCanon : RowMap (C := C) (shellChart D.chart D.coordinate D.finite D.aperture).domain
    ((promoteDatum hz hC hκ hs hreal hgamma D).shellSchema.row z)
    (shellChart D.chart D.coordinate D.finite D.aperture).correctedWeight
    ((promoteDatum hz hC hκ hs hreal hgamma D).shellSchema.weightAt z) where
  F := fun w => w ∘ shellIdx D.chart
  graph := RVCoordinateMaps.coordinate_graph_definable C _
    (shellChart D.chart D.coordinate D.finite D.aperture).domain_definable (shellIdx D.chart)
  bij := by
    let Ds := promoteDatum hz hC hκ hs hreal hgamma D
    have hrowD : Ds.chart.row z = D.chart.domain := promoteDatum_row hz hC hκ hs hreal hgamma D
    refine ⟨fun w hw => ?_, fun w hw w' hw' he => ?_, fun us hus => ?_⟩
    · show w ∘ shellIdx D.chart ∈ _
      rw [comp_shellIdx]
      exact shell_mapsTo hz hC hκ hs hreal hgamma D hw
    · have he' : w ∘ shellIdx D.chart = w' ∘ shellIdx D.chart := he
      rw [comp_shellIdx, comp_shellIdx] at he'
      have hx : w ∘ xIdx D.chart = w' ∘ xIdx D.chart := by
        funext i
        have := congrFun he' (Fin.castAdd 1 i)
        simpa using this
      have hsv : w (sIdx D.chart) = w' (sIdx D.chart) := by
        have := congrFun he' (Fin.natAdd D.chart.arity 0)
        simpa using this
      rw [shell_canonical D.chart D.aperture hw, shell_canonical D.chart D.aperture hw', hx, hsv]
    · have hus' : Fin.append z us ∈ Ds.shellDom := hus
      rw [DatumSchema.append_decomp_one us] at hus'
      obtain ⟨hu, hs0, h1, t, ht, hle⟩ := (Ds.mem_shellDom z _ _).mp hus'
      have hu' : (fun i => us (Fin.castAdd 1 i)) ∈ D.chart.domain := by
        rw [← hrowD]; exact hu
      obtain ⟨-, rfl⟩ := (promoteDatum_apRow hz hC hκ hs hreal hgamma D _ t).mp ht
      let x := join 1 D.chart.arity (fun i => us (Fin.castAdd 1 i))
        ![D.aperture.aperture (fun i => us (Fin.castAdd 1 i))]
      have hx : x ∈ (graphChart D.chart D.aperture).domain := by
        refine ⟨?_, ?_⟩
        · rw [join_comp_head]; exact hu'
        · rw [join_comp_head, join_comp_tail]
      refine ⟨join 1 (1 + D.chart.arity) x ![us (Fin.natAdd D.chart.arity 0)], ?_, ?_⟩
      · apply (VariableApertureRayCancellation.annularChart_join_iff (graphChart D.chart D.aperture) (aIdx D.chart)
          (graph_aperture_nonzero D.chart D.aperture) x _).mpr
        refine ⟨hx, fun l => by fin_cases l; exact hs0, ?_, ?_⟩
        · show 1 < codeValue (us (Fin.natAdd D.chart.arity 0))
          exact h1
        · rw [graph_aperture D.chart D.aperture hx, join_comp_head]
          show codeValue (us (Fin.natAdd D.chart.arity 0)) ≤ _
          exact hle
      · show join 1 (1 + D.chart.arity) x ![us (Fin.natAdd D.chart.arity 0)] ∘ shellIdx D.chart = us
        rw [comp_shellIdx]
        have h1' : join 1 (1 + D.chart.arity) x ![us (Fin.natAdd D.chart.arity 0)] ∘ xIdx D.chart =
            fun i => us (Fin.castAdd 1 i) := by
          funext i
          simp [xIdx, join_head, x]
        have h2' : join 1 (1 + D.chart.arity) x ![us (Fin.natAdd D.chart.arity 0)] (sIdx D.chart) =
            us (Fin.natAdd D.chart.arity 0) := by
          simp [sIdx, join_tail]
        rw [h1', h2']
        exact (DatumSchema.append_decomp_one (n := D.chart.arity) us).symm
  weight := by
    intro w hw
    let Ds := promoteDatum hz hC hκ hs hreal hgamma D
    have hv := promoteDatum_valid hz hC hκ hs hreal hgamma D
    obtain ⟨hu, -, -, -⟩ := shell_points D.chart D.aperture hw
    have hrowD : Ds.chart.row z = D.chart.domain := promoteDatum_row hz hC hκ hs hreal hgamma D
    have hus := shell_mapsTo hz hC hκ hs hreal hgamma D hw
    show D.chart.volume (w ∘ xIdx D.chart) * ∏ l, codeValue (blownCoordinate D.chart D.coordinate
      (w ∘ xIdx D.chart) (w (sIdx D.chart)) l) = _
    show _ = Ds.shellSchema.weightAt z (w ∘ shellIdx D.chart)
    rw [comp_shellIdx]
    unfold ChartSchema.weightAt
    rw [DatumSchema.shellSchema_volAt hv hus, DatumSchema.shellSchema_coordAt hv hus,
      promoteDatum_volAt hz hC hκ hs hreal hgamma D hu, promoteDatum_coordAt hz hC hκ hs hreal hgamma D hu]
    rfl

end Canon

end DiamondIntegral.Section7.Lemma714Schema
