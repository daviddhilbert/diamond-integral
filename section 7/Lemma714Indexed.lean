import «section 7».Lemma714Recode

/-! Lemma 7.14, part 11: indexed realization over RV keys.

Step 3 of the proof ("descent"). Let `Q ⊆ RV^q` be a `B`-definable set of keys
with a designated coordinate `ι`: nonzero, and finite-to-one on `Q`. A chart
schema `W` with RV parameters, valid at every key, realizes as one Section 4
chart over `B` of degree `1 + d` (`indChart Q W`):

* domain `{(x, u) | x ∈ Q, u ∈ W.row x}`;
* structural map `(x, u) ↦ (x_ι, f_x(u))`;
* volume `(x, u) ↦ vol_x(u)`.

The added coordinate `x_ι` is the same on both sides of every isomorphism, so
it adds the same weight. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6
open DiamondIntegral.Section7.BoundedClasses

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {q : ℕ}

/-! ### Generic definability helpers -/

omit hM in
theorem rvs_append (n m : ℕ) : Fin.append (rvs n) (rvs m) = rvs (n + m) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp

theorem definable_rvs_of_append {n m : ℕ} {S : Set (Fin (n + m) → M)}
    (h : DefinableOverBase B (Fin.append (rvs n) (rvs m)) S) : DefinableOverBase B (rvs (n + m)) S := by
  rwa [rvs_append] at h

/-- The set of all-RV tuples with two equal coordinates. -/
theorem eq_coords_definable {n : ℕ} (i j : Fin n) :
    DefinableOverBase B (rvs n) {w : Fin n → M | w i = w j ∧ w ∈ sortedUniverse (rvs n)} := by
  have hU := BlowupChart.rv_universe_definable B n
  have h := (RVCoordinateMaps.coordinate_graph_definable B _ hU (![j] : Fin 1 → Fin n)).preimage_real (rvs n)
    (join 1 n (id : Fin n → Fin n) ![i])
  convert h using 1
  ext w
  simp only [graphOn, Set.mem_setOf_eq, comp_join, join_comp_head, join_comp_tail]
  constructor
  · rintro ⟨he, hs⟩
    refine ⟨⟨hs, ?_⟩, hs⟩
    funext l; fin_cases l; simp [he]
  · rintro ⟨⟨hs, he⟩, -⟩
    refine ⟨?_, hs⟩
    have := congrFun he 0
    simpa using this.symm

/-- From an append-layout graph to Section 4's graph layout. -/
theorem graphOn_of_append {n m : ℕ} (I : Set (Fin n → M)) (F : (Fin n → M) → (Fin m → M))
    (G : Set (Fin (n + m) → M)) (hG : DefinableOverBase B (Fin.append (rvs n) (rvs m)) G)
    (hGF : ∀ u y, Fin.append u y ∈ G ↔ u ∈ I ∧ F u = y) :
    DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn I F) := by
  have h := hG.preimage_real (fun _ : Fin (m + n) => .rv) (ChartSchema.graphIndex n m)
  convert h using 1
  ext w
  have e : w ∘ ChartSchema.graphIndex n m = Fin.append (w ∘ headIndex m n) (w ∘ tailIndex m n) := by
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [ChartSchema.graphIndex]
  simp only [graphOn, Set.mem_setOf_eq, e, hGF]
  constructor
  · intro hw
    refine ⟨hw, ?_⟩
    have hs := hG.proper _ ((hGF _ _).mpr hw)
    apply GammaBoundedProducts.all_coordinates m n (fun x => sortEval SortTag.rv x)
    · intro i
      have := hs (Fin.castAdd m i)
      rwa [Fin.append_left, Fin.append_left] at this
    · intro i
      have := hs (Fin.natAdd n i)
      rwa [Fin.append_right, Fin.append_right] at this
  · exact And.left

/-! ### Key sets -/

/-- A definable set of RV keys with a designated nonzero, finite-to-one coordinate. -/
structure KeySet (B : Base (M := M)) (q : ℕ) where
  carrier : Set (Fin q → M)
  definable : DefinableOverBase B (rvs q) carrier
  idx : Fin q
  nonzero : ∀ x ∈ carrier, NonzeroRV (x idx)
  finite : ∀ c, {x | x ∈ carrier ∧ x idx = c}.Finite

namespace KeySet
variable (Q : KeySet B q) {d : ℕ} (W : ChartSchema B (rvs q) d)

/-- The key part of a raw point `(x, u)`. -/
def keyOf {a : ℕ} (w : Fin (q + a) → M) : Fin q → M := fun i => w (Fin.castAdd a i)
/-- The row part of a raw point `(x, u)`. -/
def rowOf {a : ℕ} (w : Fin (q + a) → M) : Fin a → M := fun j => w (Fin.natAdd q j)

omit hM in
theorem append_keyOf_rowOf {a : ℕ} (w : Fin (q + a) → M) : Fin.append (keyOf w) (rowOf w) = w :=
  Fin.append_castAdd_natAdd

/-- The domain of the indexed chart. -/
def indDom : Set (Fin (q + W.arity) → M) := {w | keyOf w ∈ Q.carrier ∧ w ∈ W.domain}

theorem indDom_definable : DefinableOverBase B (rvs (q + W.arity)) (Q.indDom W) := by
  apply definable_rvs_of_append
  convert (Q.definable.preimage_real (Fin.append (rvs q) (rvs W.arity)) (Fin.castAdd W.arity)).inter
    W.domain_definable using 1
  ext w
  simp only [indDom, keyOf, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hk, hw⟩
    exact ⟨⟨hk, W.domain_definable.proper w hw⟩, hw⟩
  · rintro ⟨⟨hk, -⟩, hw⟩
    exact ⟨hk, hw⟩

omit hM in
theorem keyOf_append {a : ℕ} (x : Fin q → M) (u : Fin a → M) : keyOf (Fin.append x u) = x :=
  funext fun i => Fin.append_left x u i

omit hM in
theorem rowOf_append {a : ℕ} (x : Fin q → M) (u : Fin a → M) : rowOf (Fin.append x u) = u :=
  funext fun i => Fin.append_right x u i

theorem mem_indDom_iff (x : Fin q → M) (u : Fin W.arity → M) :
    Fin.append x u ∈ Q.indDom W ↔ x ∈ Q.carrier ∧ u ∈ W.row x := by
  change keyOf (Fin.append x u) ∈ Q.carrier ∧ _ ↔ _
  rw [keyOf_append]
  rfl

/-- The structural map of the indexed chart: the designated key coordinate,
then the structural map of the row. -/
def indCoord (w : Fin (q + W.arity) → M) : Fin (1 + d) → M :=
  Fin.append (fun _ : Fin 1 => w (Fin.castAdd W.arity Q.idx)) (W.coordAt (keyOf w) (rowOf w))

/-- The volume of the indexed chart. -/
def indVol (w : Fin (q + W.arity) → M) : Values.Gamma (M := M) := W.volAt (keyOf w) (rowOf w)

section IndChart
variable {d : ℕ} (W : ChartSchema B (rvs q) d) (hW : ∀ x ∈ Q.carrier, W.Valid x)

/-- Index of `(x, u, y_tail)` in the layout `(x, u, y)`. -/
def coordIdx (n d : ℕ) : Fin (n + d) → Fin (n + (1 + d)) :=
  Fin.append (Fin.castAdd (1 + d)) (fun i => Fin.natAdd n (Fin.natAdd 1 i))

/-- The append-layout graph of the structural map of the indexed chart. -/
def indCoordSet : Set (Fin ((q + W.arity) + (1 + d)) → M) :=
  {v | (fun i => v (Fin.castAdd (1 + d) i)) ∈ Q.indDom W ∧
      v ∈ sortedUniverse (Fin.append (rvs (q + W.arity)) (rvs (1 + d)))} ∩
    ({v | v (Fin.natAdd (q + W.arity) (Fin.castAdd d 0)) = v (Fin.castAdd (1 + d) (Fin.castAdd W.arity Q.idx)) ∧
      v ∈ sortedUniverse (Fin.append (rvs (q + W.arity)) (rvs (1 + d)))} ∩
     {v | v ∘ coordIdx (q + W.arity) d ∈ W.coord ∧
      v ∈ sortedUniverse (Fin.append (rvs (q + W.arity)) (rvs (1 + d)))})

theorem indCoordSet_definable :
    DefinableOverBase B (Fin.append (rvs (q + W.arity)) (rvs (1 + d))) (Q.indCoordSet W) := by
  have h1 := (Q.indDom_definable W).preimage_real (Fin.append (rvs (q + W.arity)) (rvs (1 + d)))
    (Fin.castAdd (1 + d))
  have h2 := eq_coords_definable (B := B) (M := M) (Fin.natAdd (q + W.arity) (Fin.castAdd d 0))
    (Fin.castAdd (1 + d) (Fin.castAdd W.arity Q.idx))
  rw [← rvs_append] at h2
  have h3 := W.coord_definable.preimage_real (Fin.append (rvs (q + W.arity)) (rvs (1 + d))) (coordIdx (q + W.arity) d)
  exact h1.inter (h2.inter h3)

variable {W}

theorem indDom_key {w : Fin (q + W.arity) → M} (hw : w ∈ Q.indDom W) : keyOf w ∈ Q.carrier := hw.1

theorem indDom_row {w : Fin (q + W.arity) → M} (hw : w ∈ Q.indDom W) : rowOf w ∈ W.row (keyOf w) := by
  change Fin.append (keyOf w) (rowOf w) ∈ W.domain
  rw [append_keyOf_rowOf]
  exact hw.2

include hW in
theorem mem_indCoordSet (u : Fin (q + W.arity) → M) (y : Fin (1 + d) → M) :
    Fin.append u y ∈ Q.indCoordSet W ↔ u ∈ Q.indDom W ∧ Q.indCoord W u = y := by
  have e1 : (fun i => Fin.append u y (Fin.castAdd (1 + d) i)) = u := funext fun i => Fin.append_left u y i
  have e2 : Fin.append u y ∘ coordIdx (q + W.arity) d =
      Fin.append (Fin.append (keyOf u) (rowOf u)) (fun i => y (Fin.natAdd 1 i)) := by
    rw [append_keyOf_rowOf]
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [coordIdx]
  have e3 : Fin.append u y (Fin.natAdd (q + W.arity) (Fin.castAdd d 0)) = y (Fin.castAdd d 0) :=
    Fin.append_right u y _
  have e4 : Fin.append u y (Fin.castAdd (1 + d) (Fin.castAdd W.arity Q.idx)) = u (Fin.castAdd W.arity Q.idx) :=
    Fin.append_left u y _
  simp only [indCoordSet, Set.mem_inter_iff, Set.mem_setOf_eq, e1, e2, e3, e4]
  constructor
  · rintro ⟨⟨hu, -⟩, ⟨he, -⟩, ⟨hc, -⟩⟩
    refine ⟨hu, ?_⟩
    have hco := ((ChartSchema.coordRow_iff (hW _ (Q.indDom_key hu)) _ _).mp hc).2
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · fin_cases l
      simp only [indCoord, Fin.append_left]
      exact he.symm
    · simp only [indCoord, Fin.append_right]
      exact congrFun hco l
  · rintro ⟨hu, rfl⟩
    have hv := hW _ (Q.indDom_key hu)
    have hr := Q.indDom_row hu
    have hy : ∀ i, sortEval (rvs (1 + d) i) (Q.indCoord W u i) := by
      intro i
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simp only [indCoord, Fin.append_left]
        have := (Q.indDom_definable W).proper u hu (Fin.castAdd W.arity Q.idx)
        exact this
      · simp only [indCoord, Fin.append_right]
        exact (ChartSchema.coordAt_proper hv hr l).1
    have hs : Fin.append u (Q.indCoord W u) ∈ sortedUniverse (Fin.append (rvs (q + W.arity)) (rvs (1 + d))) :=
      sorted_append (fun i => (Q.indDom_definable W).proper u hu i) hy
    refine ⟨⟨hu, hs⟩, ⟨?_, hs⟩, ⟨?_, hs⟩⟩
    · simp [indCoord]
    · have hfe : (fun i => Q.indCoord W u (Fin.natAdd 1 i)) = W.coordAt (keyOf u) (rowOf u) := by
        funext i; simp [indCoord]
      rw [hfe]
      exact ChartSchema.coordRow_coordAt hv hr

include hW in
theorem indCoord_finite_fibres (t : Fin (1 + d) → M) :
    {w | w ∈ Q.indDom W ∧ Q.indCoord W w = t}.Finite := by
  let tt : Fin d → M := fun i => t (Fin.natAdd 1 i)
  let Kt := {x | x ∈ Q.carrier ∧ x Q.idx = t (Fin.castAdd d 0)}
  have hR : ∀ x ∈ Kt, {u : Fin W.arity → M | W.coordRow x u tt}.Finite := by
    intro x hx
    by_cases hs : ∀ j, sortEval (rvs d j) (tt j)
    · exact ((hW x hx.1).map.2.2.2 tt hs).1
    · refine Set.Finite.subset Set.finite_empty ?_
      intro u hu
      exact hs (mem_rows_sorted (rvs q) (rvs W.arity) (rvs d) W.coord_definable hu).2
  apply ((Q.finite _).biUnion (fun x hx => (hR x hx).image (Fin.append x))).subset
  rintro w ⟨hw, he⟩
  refine Set.mem_biUnion (x := keyOf w) ⟨Q.indDom_key hw, ?_⟩ ⟨rowOf w, ?_, append_keyOf_rowOf w⟩
  · have := congrFun he (Fin.castAdd d 0)
    simpa [indCoord, keyOf] using this
  · have hco : W.coordAt (keyOf w) (rowOf w) = tt := by
      funext i
      have := congrFun he (Fin.natAdd 1 i)
      simpa [indCoord] using this
    have := ChartSchema.coordRow_coordAt (hW _ (Q.indDom_key hw)) (Q.indDom_row hw)
    rw [hco] at this
    exact this

include hW in
theorem indVol_definable :
    DefinableOverBase B (fun _ : Fin ((q + W.arity) + 1) => .rv)
      {w | Fin.tail w ∈ Q.indDom W ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = indVol W (Fin.tail w)} := by
  have h1 := (Q.indDom_definable W).preimage_real (fun _ : Fin ((q + W.arity) + 1) => .rv) Fin.succ
  have h2 := W.volume_definable.preimage_real (fun _ : Fin ((q + W.arity) + 1) => .rv) (ChartSchema.volIndex (q + W.arity))
  convert h1.inter h2 using 1
  ext w
  have e : w ∘ ChartSchema.volIndex (q + W.arity) =
      Fin.append (Fin.append (keyOf (Fin.tail w)) (rowOf (Fin.tail w))) (fun _ : Fin 1 => w 0) := by
    rw [append_keyOf_rowOf]
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [ChartSchema.volIndex, Fin.tail]
  have et : w ∘ Fin.succ = Fin.tail w := rfl
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, e, et]
  constructor
  · rintro ⟨hw, hn, hv⟩
    have hrow := Q.indDom_row hw
    have hvr := (ChartSchema.volRow_iff (hW _ (Q.indDom_key hw)) _ (w 0)).mpr ⟨hrow, hn, hv⟩
    have hs : w ∈ sortedUniverse (fun _ : Fin ((q + W.arity) + 1) => SortTag.rv) := by
      intro i
      refine Fin.cases hn.1 (fun j => ?_) i
      exact (Q.indDom_definable W).proper _ hw j
    exact ⟨⟨hw, hs⟩, hvr, hs⟩
  · rintro ⟨⟨hw, -⟩, hvr, -⟩
    obtain ⟨-, hn, hv⟩ := (ChartSchema.volRow_iff (hW _ (Q.indDom_key hw)) _ (w 0)).mp hvr
    exact ⟨hw, hn, hv⟩

include hW in
theorem indCoord_proper {w : Fin (q + W.arity) → M} (hw : w ∈ Q.indDom W) : Proper (Q.indCoord W w) := by
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [indCoord, Fin.append_left]
    exact Q.nonzero _ (Q.indDom_key hw)
  · simp only [indCoord, Fin.append_right]
    exact ChartSchema.coordAt_proper (hW _ (Q.indDom_key hw)) (Q.indDom_row hw) l

variable (W) in
/-- **The indexed chart** of a schema valid at every key, over `B`, of degree `1 + d`. -/
def indChart : Chart B (1 + d) where
  arity := q + W.arity
  domain := Q.indDom W
  domain_definable := Q.indDom_definable W
  coordinate := Q.indCoord W
  coordinate_definable := graphOn_of_append _ _ _ (Q.indCoordSet_definable W) (Q.mem_indCoordSet hW)
  coordinate_proper := fun _ hw => Q.indCoord_proper hW hw
  finite_fibres := Q.indCoord_finite_fibres hW
  volume := indVol W
  volume_definable := Q.indVol_definable hW

end IndChart

/-! ### Weights of indexed charts -/

section IndWeight
variable {d : ℕ} {W : ChartSchema B (rvs q) d} (hW : ∀ x ∈ Q.carrier, W.Valid x)

theorem indChart_weight (w : Fin (q + W.arity) → M) :
    (Q.indChart W hW).correctedWeight w = codeValue (w (Fin.castAdd W.arity Q.idx)) * W.weightAt (keyOf w) (rowOf w) := by
  change W.volAt (keyOf w) (rowOf w) * ∏ i, codeValue (Q.indCoord W w i) = _
  rw [Fin.prod_univ_add]
  simp only [indCoord, Fin.append_left, Fin.append_right, Finset.univ_unique, Finset.prod_singleton]
  unfold ChartSchema.weightAt
  exact mul_left_comm _ _ _

end IndWeight

/-! ### Indexed isomorphisms -/

section IndIso
variable {d : ℕ} {X Y : ChartSchema B (rvs q) d} (hX : ∀ x ∈ Q.carrier, X.Valid x)
  (hY : ∀ x ∈ Q.carrier, Y.Valid x) (Φ : IsoSchema X Y) (hΦ : ∀ x ∈ Q.carrier, Φ.Valid x)

/-- The row map of an isomorphism schema at `x`, by choice. -/
def isoRaw (x : Fin q → M) (u : Fin X.arity → M) : Fin Y.arity → M :=
  if h : ∃ v, Φ.graphRow x u v then h.choose else fun _ => iRVZero

/-- The underlying map of the indexed isomorphism. -/
def indIsoFun (w : Fin (q + X.arity) → M) : Fin (q + Y.arity) → M :=
  Fin.append (keyOf w) (isoRaw Φ (keyOf w) (rowOf w))

variable {Φ}

include hΦ in
theorem isoRaw_graph {x : Fin q → M} (hx : x ∈ Q.carrier) {u : Fin X.arity → M} (hu : u ∈ X.row x) :
    Φ.graphRow x u (isoRaw Φ x u) := by
  have h : ∃ v, Φ.graphRow x u v := ((hΦ x hx).map_exists hu).exists
  rw [isoRaw, dif_pos h]
  exact h.choose_spec

include hΦ in
theorem isoRaw_eq {x : Fin q → M} (hx : x ∈ Q.carrier) {u : Fin X.arity → M} {v : Fin Y.arity → M}
    (h : Φ.graphRow x u v) : isoRaw Φ x u = v :=
  ((hΦ x hx).map_exists ((hΦ x hx).source_mem h)).unique (Q.isoRaw_graph hΦ hx ((hΦ x hx).source_mem h)) h

include hΦ in
theorem indIsoFun_bijOn : Set.BijOn (indIsoFun Φ) (Q.indDom X) (Q.indDom Y) := by
  refine ⟨fun w hw => ?_, fun w hw w' hw' he => ?_, fun w hw => ?_⟩
  · have hk := Q.indDom_key hw
    rw [indIsoFun, Q.mem_indDom_iff]
    exact ⟨hk, (hΦ _ hk).target_mem (Q.isoRaw_graph hΦ hk (Q.indDom_row hw))⟩
  · have hk : keyOf w = keyOf w' := by
      have := congrArg keyOf he
      simpa [indIsoFun, keyOf_append] using this
    have hr : isoRaw Φ (keyOf w) (rowOf w) = isoRaw Φ (keyOf w') (rowOf w') := by
      have := congrArg rowOf he
      simpa [indIsoFun, rowOf_append] using this
    have h1 := Q.isoRaw_graph hΦ (Q.indDom_key hw) (Q.indDom_row hw)
    have h2 := Q.isoRaw_graph hΦ (Q.indDom_key hw') (Q.indDom_row hw')
    have h2' : Φ.graphRow (keyOf w) (rowOf w') (isoRaw Φ (keyOf w) (rowOf w)) := by
      rw [hr, hk]; exact h2
    have hrow := (hΦ _ (Q.indDom_key hw)).inj h1 h2'
    rw [← append_keyOf_rowOf w, ← append_keyOf_rowOf w', hk, hrow]
  · have hk := Q.indDom_key hw
    obtain ⟨u, hu⟩ := (hΦ _ hk).surj (Q.indDom_row hw)
    refine ⟨Fin.append (keyOf w) u, (Q.mem_indDom_iff X _ _).mpr ⟨hk, (hΦ _ hk).source_mem hu⟩, ?_⟩
    rw [indIsoFun, keyOf_append, rowOf_append, Q.isoRaw_eq hΦ hk hu, append_keyOf_rowOf]

end IndIso

end KeySet

end DiamondIntegral.Section7.Lemma714Schema
