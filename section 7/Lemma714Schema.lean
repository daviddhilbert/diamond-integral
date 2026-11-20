import «section 7».Lemma714Witness

/-! Lemma 7.14, part 2: uniform families of Section 4 charts (chart schemata).

A chart schema over a base `B` with parameter sorts `sp : Fin p → SortTag` is a
triple of `B`-definable sets whose rows at a parameter tuple `z` are the data of
a Section 4 chart of degree `d`:

* `domain ⊆ M^(p + a)`: the row `{u | z ++ u ∈ domain}` is the domain;
* `coord ⊆ M^((p + a) + d)`: the row is the graph of the structural map;
* `volume ⊆ M^((p + a) + 1)`: `(z, u, c)` with `codeValue c` the volume at `u`;

together with a natural-number bound for the fibres of the structural map
(the device of [Yin, Lemma 6.14] that makes "finite-to-one" first order).

`ChartSchema.Valid W z` says that the row at `z` is a bounded chart. When it
holds, `W.toChart z` is that chart over the base `B ∪ z` (`baseAt B z`). The
schemata are the uniform witnesses of the proof of Lemma 7.14. This is the
annular, Γ-volume analogue of upstream `GammaFiniteRVSchema`.

The layouts follow upstream integration-in-ACVF (`Fin.append z u`), so that
the generic first-order combinators of `IntegrationSection6` apply. -/

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

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- All-RV sorts. -/
abbrev rvs (n : ℕ) : Fin n → SortTag := fun _ => .rv

/-- The base `B ∪ z`. -/
abbrev baseAt (B : Base (M := M)) {p : ℕ} (z : Fin p → M) : Base (M := M) :=
  ⟨B.real ∪ Set.range z, B.gamma⟩

/-! ### Rows of definable families -/

section Rows
variable {B : Base (M := M)} {p a d : ℕ}

omit hM in
theorem append_assoc_split (z : Fin p → M) (w : Fin (a + d) → M) :
    Fin.append (Fin.append z (fun i => w (Fin.castAdd d i))) (fun j => w (Fin.natAdd a j)) =
      Fin.append z w ∘ Fin.cast (Nat.add_assoc p a d) := by
  rw [Fin.append_assoc]
  congr 2
  exact Fin.append_castAdd_natAdd

/-- The row of a `B`-definable set at a parameter `z`, in two blocks, is
definable over `B ∪ z`. -/
theorem row2_definable (sp : Fin p → SortTag) (sx : Fin a → SortTag) (sy : Fin d → SortTag)
    {D : Set (Fin ((p + a) + d) → M)} (hD : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) D)
    (z : Fin p → M) :
    DefinableOverBase (baseAt B z) (Fin.append sx sy)
      {w : Fin (a + d) → M | Fin.append (Fin.append z (fun i => w (Fin.castAdd d i)))
        (fun j => w (Fin.natAdd a j)) ∈ D} := by
  have hV := hD.preimage_real (Fin.append sp (Fin.append sx sy)) (Fin.cast (Nat.add_assoc p a d))
  have hR := gamma_tuple_parameter_specialize sp (Fin.append sx sy) z hV
  convert hR using 1
  ext w
  simp only [Set.mem_setOf_eq]
  rw [append_assoc_split]
  constructor
  · intro hw
    refine ⟨hw, ?_⟩
    have hs := hD.proper _ hw
    intro i
    have := hs (Fin.cast (Nat.add_assoc p a d).symm i)
    rw [Fin.append_assoc] at this
    simpa using this
  · exact And.left

omit hM in
theorem append_assoc_apply {α : Type*} (z : Fin p → α) (x : Fin a → α) (y : Fin d → α) (i : Fin (p + (a + d))) :
    Fin.append (Fin.append z x) y (Fin.cast (Nat.add_assoc p a d).symm i) = Fin.append z (Fin.append x y) i := by
  rw [Fin.append_assoc]
  simp

/-- Universal statements over two-block rows are definable. -/
theorem row2_forall_definable (sp : Fin p → SortTag) (sx : Fin a → SortTag) (sy : Fin d → SortTag)
    {D C : Set (Fin ((p + a) + d) → M)} (hD : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) D)
    (hC : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) C) :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ (x : Fin a → M) (y : Fin d → M), Fin.append (Fin.append z x) y ∈ D →
        Fin.append (Fin.append z x) y ∈ C} := by
  let st := Fin.append sp (Fin.append sx sy)
  have hD' := hD.preimage_real st (Fin.cast (Nat.add_assoc p a d))
  have hC' := hC.preimage_real st (Fin.cast (Nat.add_assoc p a d))
  have h := gamma_family_row_subset_definable sp (Fin.append sx sy) hD' hC'
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hall⟩
    refine ⟨hz, fun w hw => ⟨?_, hw.2⟩⟩
    have h1 := hall (fun i => w (Fin.castAdd d i)) (fun j => w (Fin.natAdd a j))
    rw [append_assoc_split] at h1
    exact h1 hw.1
  · rintro ⟨hz, hall⟩
    refine ⟨hz, fun x y hxy => ?_⟩
    have hs := hD.proper _ hxy
    have hw : Fin.append z (Fin.append x y) ∈ sortedUniverse st := by
      intro i
      have := hs (Fin.cast (Nat.add_assoc p a d).symm i)
      rw [append_assoc_apply, append_assoc_apply] at this
      exact this
    have e : Fin.append z (Fin.append x y) ∘ Fin.cast (Nat.add_assoc p a d) =
        Fin.append (Fin.append z x) y := (Fin.append_assoc z x y).symm
    have h2 := hall (Fin.append x y) ⟨by rw [e]; exact hxy, hw⟩
    rw [e] at h2
    exact h2.1

omit hM in
theorem sorted_append {n m : ℕ} {sa : Fin n → SortTag} {sb : Fin m → SortTag} {x : Fin n → M} {y : Fin m → M}
    (hx : ∀ i, sortEval (sa i) (x i)) (hy : ∀ j, sortEval (sb j) (y j)) :
    Fin.append x y ∈ sortedUniverse (Fin.append sa sb) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, Fin.append_left]
    exact hx i
  · rw [Fin.append_right, Fin.append_right]
    exact hy i

theorem mem_rows_sorted (sp : Fin p → SortTag) (sx : Fin a → SortTag) (sy : Fin d → SortTag)
    {D : Set (Fin ((p + a) + d) → M)} (hD : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) D)
    {z : Fin p → M} {x : Fin a → M} {y : Fin d → M} (h : Fin.append (Fin.append z x) y ∈ D) :
    (∀ i, sortEval (sx i) (x i)) ∧ ∀ j, sortEval (sy j) (y j) := by
  constructor
  · intro i
    have := hD.proper _ h (Fin.castAdd d (Fin.natAdd p i))
    rwa [Fin.append_left, Fin.append_right, Fin.append_left, Fin.append_right] at this
  · intro j
    have := hD.proper _ h (Fin.natAdd (p + a) j)
    rwa [Fin.append_right, Fin.append_right] at this

end Rows

/-! ### Chart schemata -/

/-- A uniform family of Section 4 charts of degree `d`, parametrized by
`z : Fin p → M` of sorts `sp`. -/
structure ChartSchema (B : Base (M := M)) {p : ℕ} (sp : Fin p → SortTag) (d : ℕ) where
  arity : ℕ
  domain : Set (Fin (p + arity) → M)
  domain_definable : DefinableOverBase B (Fin.append sp (rvs arity)) domain
  coord : Set (Fin ((p + arity) + d) → M)
  coord_definable : DefinableOverBase B (Fin.append (Fin.append sp (rvs arity)) (rvs d)) coord
  volume : Set (Fin ((p + arity) + 1) → M)
  volume_definable : DefinableOverBase B (Fin.append (Fin.append sp (rvs arity)) (rvs 1)) volume
  bound : ℕ

namespace ChartSchema
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag} {d : ℕ} (W : ChartSchema B sp d)

/-- The domain row at `z`. -/
def row (z : Fin p → M) : Set (Fin W.arity → M) := {u | Fin.append z u ∈ W.domain}

/-- The structural-map row at `z`. -/
def coordRow (z : Fin p → M) (u : Fin W.arity → M) (y : Fin d → M) : Prop :=
  Fin.append (Fin.append z u) y ∈ W.coord

/-- The volume row at `z`: `c` is a code of the volume at `u`. -/
def volRow (z : Fin p → M) (u : Fin W.arity → M) (c : M) : Prop :=
  Fin.append (Fin.append z u) (fun _ : Fin 1 => c) ∈ W.volume

/-- The row at `z` is a bounded chart of degree `d`. -/
structure Valid (z : Fin p → M) : Prop where
  map : finiteMapRowValid sp (rvs d) W.domain W.coord W.bound z
  proper : ∀ u y, W.coordRow z u y → Proper y
  vol_total : ∀ u ∈ W.row z, ∃ c, W.volRow z u c
  vol_dom : ∀ u c, W.volRow z u c → u ∈ W.row z ∧ NonzeroRV c
  vol_same : ∀ u c c', W.volRow z u c → NonzeroRV c → NonzeroRV c' →
    (W.volRow z u c' ↔ codeValue c' = codeValue c)
  bounded : ∃ lo hi : Values.Gamma (M := M), ∀ u ∈ W.row z, ∀ i, NonzeroRV (u i) →
    lo ≤ codeValue (u i) ∧ codeValue (u i) ≤ hi

variable {W}

theorem Valid.sorted {z : Fin p → M} (hz : W.Valid z) : ∀ i, sortEval (sp i) (z i) := hz.map.1

theorem Valid.coord_exists {z : Fin p → M} (hz : W.Valid z) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    ∃! y : Fin d → M, W.coordRow z u y := hz.map.2.1 u hu

theorem Valid.coord_dom {z : Fin p → M} (hz : W.Valid z) {u : Fin W.arity → M} {y : Fin d → M}
    (h : W.coordRow z u y) : u ∈ W.row z := hz.map.2.2.1 u y h

variable (W)

/-- The structural map at `z`, by choice on the row (the constant `0` tuple
elsewhere). -/
def coordAt (z : Fin p → M) (u : Fin W.arity → M) : Fin d → M :=
  if h : ∃ y, W.coordRow z u y then h.choose else fun _ => iRVZero

/-- The volume at `z`, by choice on the row (`1` elsewhere). -/
def volAt (z : Fin p → M) (u : Fin W.arity → M) : Values.Gamma (M := M) :=
  if h : ∃ c, W.volRow z u c then codeValue h.choose else 1

variable {W}

theorem coordRow_coordAt {z : Fin p → M} (hz : W.Valid z) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    W.coordRow z u (W.coordAt z u) := by
  have h : ∃ y, W.coordRow z u y := (hz.coord_exists hu).exists
  rw [coordAt, dif_pos h]
  exact h.choose_spec

theorem coordRow_iff {z : Fin p → M} (hz : W.Valid z) (u : Fin W.arity → M) (y : Fin d → M) :
    W.coordRow z u y ↔ u ∈ W.row z ∧ W.coordAt z u = y := by
  constructor
  · intro h
    have hu := hz.coord_dom h
    exact ⟨hu, (hz.coord_exists hu).unique (coordRow_coordAt hz hu) h⟩
  · rintro ⟨hu, rfl⟩
    exact coordRow_coordAt hz hu

theorem volRow_iff {z : Fin p → M} (hz : W.Valid z) (u : Fin W.arity → M) (c : M) :
    W.volRow z u c ↔ u ∈ W.row z ∧ NonzeroRV c ∧ codeValue c = W.volAt z u := by
  constructor
  · intro h
    obtain ⟨hu, hc⟩ := hz.vol_dom u c h
    have hex : ∃ c, W.volRow z u c := ⟨c, h⟩
    refine ⟨hu, hc, ?_⟩
    rw [volAt, dif_pos hex]
    exact (hz.vol_same u hex.choose c hex.choose_spec (hz.vol_dom u _ hex.choose_spec).2 hc).mp h
  · rintro ⟨hu, hc, he⟩
    obtain ⟨c₀, h₀⟩ := hz.vol_total u hu
    have hex : ∃ c, W.volRow z u c := ⟨c₀, h₀⟩
    rw [volAt, dif_pos hex] at he
    exact (hz.vol_same u hex.choose c hex.choose_spec (hz.vol_dom u _ hex.choose_spec).2 hc).mpr he

/-! ### The chart of a valid row -/

theorem row_definable (z : Fin p → M) :
    DefinableOverBase (baseAt B z) (rvs W.arity) (W.row z) :=
  gamma_tuple_parameter_specialize sp (rvs W.arity) z W.domain_definable

/-- The structural-map row in two blocks is definable over `B ∪ z`. -/
theorem coordRow_definable (z : Fin p → M) :
    DefinableOverBase (baseAt B z) (Fin.append (rvs W.arity) (rvs d))
      {w : Fin (W.arity + d) → M | W.coordRow z (fun i => w (Fin.castAdd d i)) (fun j => w (Fin.natAdd W.arity j))} :=
  row2_definable sp (rvs W.arity) (rvs d) W.coord_definable z

theorem volRow_definable (z : Fin p → M) :
    DefinableOverBase (baseAt B z) (Fin.append (rvs W.arity) (rvs 1))
      {w : Fin (W.arity + 1) → M | W.volRow z (fun i => w (Fin.castAdd 1 i)) (w (Fin.natAdd W.arity 0))} := by
  have h := row2_definable sp (rvs W.arity) (rvs 1) W.volume_definable z
  convert h using 3 with w
  unfold volRow
  congr! 2
  funext j
  fin_cases j
  rfl

theorem coordAt_proper {z : Fin p → M} (hz : W.Valid z) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    Proper (W.coordAt z u) :=
  hz.proper u _ (coordRow_coordAt hz hu)

theorem row_rv {z : Fin p → M} {u : Fin W.arity → M} (hu : u ∈ W.row z) (i : Fin W.arity) :
    sortEval SortTag.rv (u i) := by
  have h := W.domain_definable.proper _ hu (Fin.natAdd p i)
  have e : Fin.append z u (Fin.natAdd p i) = u i := Fin.append_right z u i
  have e2 : (Fin.append sp (rvs W.arity)) (Fin.natAdd p i) = SortTag.rv := Fin.append_right sp (rvs W.arity) i
  rw [e, e2] at h
  exact h

/-- The index map from the graph layout `Fin (d + a)` of Section 4 to the
append layout `Fin (a + d)`. -/
def graphIndex (a d : ℕ) : Fin (a + d) → Fin (d + a) := Fin.append (headIndex d a) (tailIndex d a)

theorem coordinate_graph_definable {z : Fin p → M} (hz : W.Valid z) :
    DefinableOverBase (baseAt B z) (fun _ : Fin (d + W.arity) => .rv) (graphOn (W.row z) (W.coordAt z)) := by
  have h := (W.coordRow_definable z).preimage_real (fun _ : Fin (d + W.arity) => .rv) (graphIndex W.arity d)
  convert h using 1
  ext w
  simp only [graphOn, Set.mem_setOf_eq, graphIndex, Function.comp_def, Fin.append_left, Fin.append_right]
  rw [coordRow_iff hz]
  constructor
  · rintro ⟨hu, he⟩
    refine ⟨⟨hu, he⟩, ?_⟩
    apply GammaBoundedProducts.all_coordinates d W.arity (fun x => sortEval SortTag.rv x) w
    · exact fun i => row_rv hu i
    · intro j
      have := (coordAt_proper hz hu j).1
      rw [he] at this
      exact this
  · rintro ⟨⟨hu, he⟩, -⟩
    exact ⟨hu, he⟩

theorem coordAt_finite_fibres {z : Fin p → M} (hz : W.Valid z) (t : Fin d → M) :
    {u | u ∈ W.row z ∧ W.coordAt z u = t}.Finite := by
  by_cases ht : ∀ j, sortEval (rvs d j) (t j)
  · refine (hz.map.2.2.2 t ht).1.subset ?_
    rintro u ⟨hu, rfl⟩
    exact coordRow_coordAt hz hu
  · convert Set.finite_empty
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hu rfl
    exact ht (fun j => (coordAt_proper hz hu j).1)

/-- The index map from the volume layout `Fin (a + 1)` (code first) to the
append layout. -/
def volIndex (a : ℕ) : Fin (a + 1) → Fin (a + 1) := Fin.append Fin.succ (fun _ : Fin 1 => 0)

theorem volume_set_definable {z : Fin p → M} (hz : W.Valid z) :
    DefinableOverBase (baseAt B z) (fun _ : Fin (W.arity + 1) => .rv)
      {w | Fin.tail w ∈ W.row z ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = W.volAt z (Fin.tail w)} := by
  have h := (W.volRow_definable z).preimage_real (fun _ : Fin (W.arity + 1) => .rv) (volIndex W.arity)
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, volIndex, Function.comp_def, Fin.append_left, Fin.append_right]
  rw [volRow_iff hz]
  constructor
  · rintro hw
    refine ⟨hw, fun l => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hw.2.1.1
    · exact row_rv hw.1 i
  · exact And.left

/-- The chart of a valid row, over `B ∪ z`. -/
def toChart (z : Fin p → M) (hz : W.Valid z) : Chart (baseAt B z) d where
  arity := W.arity
  domain := W.row z
  domain_definable := W.row_definable z
  coordinate := W.coordAt z
  coordinate_definable := coordinate_graph_definable hz
  coordinate_proper := fun _ hu => coordAt_proper hz hu
  finite_fibres := coordAt_finite_fibres hz
  volume := W.volAt z
  volume_definable := volume_set_definable hz

theorem toChart_domainBounded {z : Fin p → M} (hz : W.Valid z) :
    RVMeasuredBounds.DomainBounded (W.toChart z hz) := by
  obtain ⟨lo, hi, h⟩ := hz.bounded
  refine ⟨max hi lo⁻¹, fun u hu i hi0 => ?_⟩
  obtain ⟨h1, h2⟩ := h u hu i hi0
  constructor
  · calc (max hi lo⁻¹)⁻¹ ≤ (lo⁻¹)⁻¹ := inv_le_inv_iff.mpr (le_max_right _ _)
      _ = lo := inv_inv lo
      _ ≤ _ := h1
  · exact h2.trans (le_max_left _ _)

/-- The bounded object of a valid row, over `B ∪ z`. -/
def toObj (z : Fin p → M) (hz : W.Valid z) : RVBoundedCharts.BoundedChart (baseAt B z) d :=
  ⟨W.toChart z hz, toChart_domainBounded hz⟩

/-! ### The validity locus is definable -/

section ValidDefinable
variable (W)

omit hM in
theorem append_comp_castAdd {α : Type*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) :
    Fin.append u v ∘ Fin.castAdd n = u := funext (Fin.append_left u v)

omit hM in
theorem append_comp_natAdd {α : Type*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) :
    Fin.append u v ∘ Fin.natAdd m = v := funext (Fin.append_right u v)

theorem proper_set_definable (n m : ℕ) (sn : Fin n → SortTag) (π : Fin m → Fin n) :
    DefinableOverBase B sn {w : Fin n → M | w ∘ π ∈ {z | Proper z} ∧ w ∈ sortedUniverse sn} :=
  (GammaOrderLogic.proper_definable_base B m).preimage_real sn π

theorem proper_one_iff (x : M) : Proper (fun _ : Fin 1 => x) ↔ NonzeroRV x :=
  ⟨fun h => h 0, fun h _ => h⟩

theorem valid_proper_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ (u : Fin W.arity → M) (y : Fin d → M), Fin.append (Fin.append z u) y ∈ W.coord →
        Fin.append (Fin.append z u) y ∈
          {w | w ∘ Fin.natAdd (p + W.arity) ∈ {z | Proper z} ∧
            w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs W.arity)) (rvs d))}} :=
  row2_forall_definable sp (rvs W.arity) (rvs d) W.coord_definable
    (proper_set_definable _ _ _ (Fin.natAdd (p + W.arity)))

theorem valid_volTotal_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ u : Fin W.arity → M, Fin.append z u ∈ W.domain →
        Fin.append z u ∈ {w | ∃ b : Fin 1 → M, Fin.append w b ∈ W.volume}} :=
  gamma_family_row_subset_definable sp (rvs W.arity) W.domain_definable
    (gamma_family_row_exists_definable (Fin.append sp (rvs W.arity)) (rvs 1) W.volume_definable)

theorem valid_volDom_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ (u : Fin W.arity → M) (y : Fin 1 → M), Fin.append (Fin.append z u) y ∈ W.volume →
        Fin.append (Fin.append z u) y ∈
          {w | w ∘ Fin.castAdd 1 ∈ W.domain ∧ w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs W.arity)) (rvs 1))} ∩
          {w | w ∘ Fin.natAdd (p + W.arity) ∈ {z | Proper z} ∧
            w ∈ sortedUniverse (Fin.append (Fin.append sp (rvs W.arity)) (rvs 1))}} :=
  row2_forall_definable sp (rvs W.arity) (rvs 1) W.volume_definable
    ((W.domain_definable.preimage_real _ (Fin.castAdd 1)).inter
      (proper_set_definable _ _ _ (Fin.natAdd (p + W.arity))))

/-- Index of the first code `c` in the layout `(z, u, c, c')`. -/
def volIdx₀ (p a : ℕ) : Fin ((p + a) + 1) → Fin ((p + a) + 2) :=
  Fin.append (Fin.castAdd 2) (fun _ => Fin.natAdd (p + a) 0)

/-- Index of the second code `c'` in the layout `(z, u, c, c')`. -/
def volIdx₁ (p a : ℕ) : Fin ((p + a) + 1) → Fin ((p + a) + 2) :=
  Fin.append (Fin.castAdd 2) (fun _ => Fin.natAdd (p + a) 1)

theorem valid_volSame_definable :
    let st := Fin.append (Fin.append sp (rvs W.arity)) (rvs 2)
    let V₀ := {w : Fin ((p + W.arity) + 2) → M | w ∘ volIdx₀ p W.arity ∈ W.volume ∧ w ∈ sortedUniverse st}
    let V₁ := {w : Fin ((p + W.arity) + 2) → M | w ∘ volIdx₁ p W.arity ∈ W.volume ∧ w ∈ sortedUniverse st}
    let E := {w : Fin ((p + W.arity) + 2) → M |
      w ∘ ![Fin.natAdd (p + W.arity) 1, Fin.natAdd (p + W.arity) 0] ∈ {z | Proper z ∧ codeValue (z 0) = codeValue (z 1)} ∧
        w ∈ sortedUniverse st}
    let P := {w : Fin ((p + W.arity) + 2) → M | w ∘ Fin.natAdd (p + W.arity) ∈ {z | Proper z} ∧ w ∈ sortedUniverse st}
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧
      ∀ (u : Fin W.arity → M) (y : Fin 2 → M), Fin.append (Fin.append z u) y ∈ V₀ ∩ P →
        Fin.append (Fin.append z u) y ∈ (V₁ ∩ E) ∪ ((sortedUniverse st \ V₁) ∩ (sortedUniverse st \ E))} := by
  intro st V₀ V₁ E P
  have hV₀ : DefinableOverBase B st V₀ := W.volume_definable.preimage_real st (volIdx₀ p W.arity)
  have hV₁ : DefinableOverBase B st V₁ := W.volume_definable.preimage_real st (volIdx₁ p W.arity)
  have hE : DefinableOverBase B st E :=
    (VariableApertureMeasuredComparison.value_equality_definable B).preimage_real st _
  have hP : DefinableOverBase B st P := proper_set_definable _ _ _ (Fin.natAdd (p + W.arity))
  exact row2_forall_definable sp (rvs W.arity) (rvs 2) (hV₀.inter hP)
    ((hV₁.inter hE).union (hV₁.compl.inter hE.compl))

/-- The order formula `lo ≤ x ≤ hi` on the codes `(lo, hi, x)`. -/
def betweenFormula : GammaOrderLogic.Formula Empty 3 :=
  .and (.not (.lt 2 0)) (.not (.lt 1 2))

theorem between_definable :
    DefinableOverBase B (fun _ : Fin 3 => .rv)
      {z : Fin 3 → M | Proper z ∧ codeValue (z 0) ≤ codeValue (z 2) ∧ codeValue (z 2) ≤ codeValue (z 1)} := by
  have h := GammaOrderLogic.formula_definable_base B (fun e : Empty => nomatch e) (fun e => nomatch e)
    betweenFormula
  change DefinableOverBase B (fun _ : Fin 3 => .rv)
    {z | Proper z ∧ ¬ codeValue (z 2) < codeValue (z 0) ∧ ¬ codeValue (z 1) < codeValue (z 2)} at h
  convert h using 3 with z
  simp only [not_lt]

/-- The set of parameters with codes `(lo, hi)` bounding the domain row. -/
def boundSet : Set (Fin (p + 2) → M) :=
  {w | w ∈ sortedUniverse (Fin.append sp (rvs 2)) ∧ Proper (w ∘ Fin.natAdd p) ∧
    ∀ u : Fin W.arity → M, Fin.append (w ∘ Fin.castAdd 2) u ∈ W.domain → ∀ i, NonzeroRV (u i) →
      codeValue (w (Fin.natAdd p 0)) ≤ codeValue (u i) ∧ codeValue (u i) ≤ codeValue (w (Fin.natAdd p 1))}

theorem boundSet_definable : DefinableOverBase B (Fin.append sp (rvs 2)) (W.boundSet) := by
  let sw := Fin.append sp (rvs 2)
  let st := Fin.append sw (rvs W.arity)
  let ιD : Fin (p + W.arity) → Fin ((p + 2) + W.arity) :=
    Fin.append (fun i => Fin.castAdd W.arity (Fin.castAdd 2 i)) (fun j => Fin.natAdd (p + 2) j)
  have hDom : DefinableOverBase B st {v | v ∘ ιD ∈ W.domain ∧ v ∈ sortedUniverse st} :=
    W.domain_definable.preimage_real st ιD
  let lo : Fin ((p + 2) + W.arity) := Fin.castAdd W.arity (Fin.natAdd p 0)
  let hi : Fin ((p + 2) + W.arity) := Fin.castAdd W.arity (Fin.natAdd p 1)
  let Bd (i : Fin W.arity) : Set (Fin ((p + 2) + W.arity) → M) :=
    (sortedUniverse st \ {v | v ∘ ![Fin.natAdd (p + 2) i] ∈ {z | Proper z} ∧ v ∈ sortedUniverse st}) ∪
      {v | v ∘ ![lo, hi, Fin.natAdd (p + 2) i] ∈
        {z : Fin 3 → M | Proper z ∧ codeValue (z 0) ≤ codeValue (z 2) ∧ codeValue (z 2) ≤ codeValue (z 1)} ∧
        v ∈ sortedUniverse st}
  have hBd (i : Fin W.arity) : DefinableOverBase B st (Bd i) :=
    (proper_set_definable _ _ st _).compl.union (between_definable.preimage_real st _)
  have hAll := DefinableOverBase.finite_iInter Finset.univ Bd (fun i _ => hBd i)
  have hRow := gamma_family_row_subset_definable sw (rvs W.arity) hDom hAll
  have hP := proper_set_definable (M := M) (B := B) (p + 2) 2 sw (Fin.natAdd p)
  convert hRow.inter hP using 1
  ext w
  simp only [boundSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  have hιD (u : Fin W.arity → M) : Fin.append w u ∘ ιD = Fin.append (w ∘ Fin.castAdd 2) u := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ιD]
  constructor
  · rintro ⟨hw, hPw, hall⟩
    refine ⟨⟨hw, fun u hu => ?_⟩, hPw, hw⟩
    have hsu : Fin.append w u ∈ sortedUniverse st := hDom.proper _ hu
    refine ⟨hsu, fun i _ => ?_⟩
    rw [hιD] at hu
    by_cases hi0 : NonzeroRV (u i)
    · right
      refine ⟨?_, hsu⟩
      obtain ⟨h1, h2⟩ := hall u hu.1 i hi0
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simpa [lo] using hPw 0
        · simpa [hi] using hPw 1
        · exact (show NonzeroRV (Fin.append w u (Fin.natAdd (p + 2) i)) from (Fin.append_right w u i).symm ▸ hi0)
      · simpa [lo, hi] using And.intro h1 h2
    · left
      refine ⟨hsu, fun h => hi0 ?_⟩
      exact (Fin.append_right w u i) ▸ (show NonzeroRV (Fin.append w u (Fin.natAdd (p + 2) i)) from h.1 0)
  · rintro ⟨⟨hw, hall⟩, hPw, -⟩
    refine ⟨hw, hPw, fun u hu i hi0 => ?_⟩
    have hsu : Fin.append w u ∈ sortedUniverse st := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa [st] using hw l
      · have := W.domain_definable.proper _ hu (Fin.natAdd p l)
        simpa [st] using this
    have hmem : Fin.append w u ∈ {v | v ∘ ιD ∈ W.domain ∧ v ∈ sortedUniverse st} := ⟨by rw [hιD]; exact hu, hsu⟩
    obtain ⟨-, hi'⟩ := hall u hmem
    rcases hi' i (Finset.mem_univ i) with h | h
    · exact absurd (⟨fun l => by
        fin_cases l
        exact (show NonzeroRV (Fin.append w u (Fin.natAdd (p + 2) i)) from (Fin.append_right w u i).symm ▸ hi0), hsu⟩) h.2
    · simpa [lo, hi] using h.1.2

theorem valid_bounded_definable :
    DefinableOverBase B sp {z | ∃ b : Fin 2 → M, Fin.append z b ∈ W.boundSet} :=
  gamma_family_row_exists_definable sp (rvs 2) W.boundSet_definable

theorem codeValue_raw_representative (γ : Values.Gamma (M := M)) :
    codeValue (GammaParameters.raw (GammaParameters.representative γ)) = γ := by
  rw [codeValue_raw, representative_value]

theorem nonzero_raw (t : GammaParameters.Code (M := M)) : NonzeroRV (GammaParameters.raw t) :=
  ⟨raw_rv t, raw_ne_zero t⟩

theorem append_volIdx₀ (z : Fin p → M) (u : Fin W.arity → M) (y : Fin 2 → M) :
    Fin.append (Fin.append z u) y ∘ volIdx₀ p W.arity = Fin.append (Fin.append z u) (fun _ : Fin 1 => y 0) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [volIdx₀]

theorem append_volIdx₁ (z : Fin p → M) (u : Fin W.arity → M) (y : Fin 2 → M) :
    Fin.append (Fin.append z u) y ∘ volIdx₁ p W.arity = Fin.append (Fin.append z u) (fun _ : Fin 1 => y 1) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [volIdx₁]

theorem append_swap_codes (z : Fin p → M) (u : Fin W.arity → M) (y : Fin 2 → M) :
    Fin.append (Fin.append z u) y ∘ ![Fin.natAdd (p + W.arity) 1, Fin.natAdd (p + W.arity) 0] = ![y 1, y 0] := by
  funext j
  fin_cases j <;> simp

theorem volRow_iff_mem (z : Fin p → M) (u : Fin W.arity → M) (y : Fin 1 → M) :
    W.volRow z u (y 0) ↔ Fin.append (Fin.append z u) y ∈ W.volume := by
  unfold volRow
  have : (fun _ : Fin 1 => y 0) = y := by funext j; fin_cases j; rfl
  rw [this]

/-- **The validity locus of a chart schema is `B`-definable.** -/
theorem valid_definable : DefinableOverBase B sp {z | W.Valid z} := by
  have h1 := gamma_finite_map_validity_definable sp (rvs W.arity) (rvs d) W.bound
    W.domain_definable W.coord_definable
  have h := h1.inter (W.valid_proper_definable.inter (W.valid_volTotal_definable.inter
    (W.valid_volDom_definable.inter (W.valid_volSame_definable.inter W.valid_bounded_definable))))
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro hz
    refine ⟨hz.map, ⟨hz.sorted, fun u y hy => ⟨?_, W.coord_definable.proper _ hy⟩⟩,
      ⟨hz.sorted, fun u hu => ?_⟩, ⟨hz.sorted, fun u y hy => ?_⟩, ⟨hz.sorted, fun u y hy => ?_⟩, ?_⟩
    · rw [append_comp_natAdd]
      exact hz.proper u y hy
    · obtain ⟨c, hc⟩ := hz.vol_total u hu
      exact ⟨fun _ => c, hc⟩
    · obtain ⟨hu, hc⟩ := hz.vol_dom u (y 0) ((W.volRow_iff_mem z u y).mpr hy)
      have hs := W.volume_definable.proper _ hy
      refine ⟨⟨?_, hs⟩, ⟨?_, hs⟩⟩
      · rw [append_comp_castAdd]
        exact hu
      · rw [append_comp_natAdd]
        intro j
        fin_cases j
        exact hc
    · obtain ⟨⟨hv0, hs⟩, hP, -⟩ := hy
      rw [append_volIdx₀] at hv0
      rw [append_comp_natAdd] at hP
      have hv0' : W.volRow z u (y 0) := hv0
      have hiff := hz.vol_same u (y 0) (y 1) hv0' (hP 0) (hP 1)
      have hE : Proper ((Fin.append (Fin.append z u) y) ∘
          ![Fin.natAdd (p + W.arity) 1, Fin.natAdd (p + W.arity) 0]) := by
        intro j
        fin_cases j
        · simpa using hP 1
        · simpa using hP 0
      by_cases hv1 : W.volRow z u (y 1)
      · left
        refine ⟨⟨?_, hs⟩, ⟨⟨hE, ?_⟩, hs⟩⟩
        · rw [append_volIdx₁]
          exact hv1
        · simpa using hiff.mp hv1
      · right
        refine ⟨⟨hs, fun h => hv1 ?_⟩, ⟨hs, fun h => hv1 ?_⟩⟩
        · have h' := h.1
          rw [append_volIdx₁] at h'
          exact h'
        · apply hiff.mpr
          simpa using h.1.2
    · obtain ⟨lo, hi, hb⟩ := hz.bounded
      refine ⟨![GammaParameters.raw (GammaParameters.representative lo),
        GammaParameters.raw (GammaParameters.representative hi)], ?_, ?_, ?_⟩
      · intro j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using hz.sorted i
        · fin_cases i
          · simp only [Fin.append_right]
            exact (show sortEval SortTag.rv (GammaParameters.raw (GammaParameters.representative lo)) from
              (nonzero_raw (GammaParameters.representative lo)).1)
          · simp only [Fin.append_right]
            exact (show sortEval SortTag.rv (GammaParameters.raw (GammaParameters.representative hi)) from
              (nonzero_raw (GammaParameters.representative hi)).1)
      · rw [append_comp_natAdd]
        intro j
        fin_cases j
        · exact (nonzero_raw (GammaParameters.representative lo))
        · exact (nonzero_raw (GammaParameters.representative hi))
      · intro u hu i hi0
        rw [append_comp_castAdd] at hu
        simpa [codeValue_raw_representative] using hb u hu i hi0
  · rintro ⟨hmap, ⟨-, hprop⟩, ⟨-, htot⟩, ⟨-, hdom⟩, ⟨-, hsame⟩, ⟨b, hbz⟩⟩
    refine ⟨hmap, ?_, ?_, ?_, ?_, ?_⟩
    · intro u y hy
      have := (hprop u y hy).1
      rwa [append_comp_natAdd] at this
    · intro u hu
      obtain ⟨b, hb⟩ := htot u hu
      exact ⟨b 0, (W.volRow_iff_mem z u b).mpr hb⟩
    · intro u c hc
      obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hdom u (fun _ => c) hc
      rw [append_comp_castAdd] at h1
      rw [append_comp_natAdd] at h2
      exact ⟨h1, h2 0⟩
    · intro u c c' hc hc0 hc'0
      have hs := W.volume_definable.proper _ hc
      let y : Fin 2 → M := ![c, c']
      have hsy : Fin.append (Fin.append z u) y ∈
          sortedUniverse (Fin.append (Fin.append sp (rvs W.arity)) (rvs 2)) := by
        intro j
        refine Fin.addCases (fun l => ?_) (fun l => ?_) j
        · have := hs (Fin.castAdd 1 l)
          simpa using this
        · fin_cases l
          · simp only [Fin.append_right]
            exact (show sortEval SortTag.rv c from hc0.1)
          · simp only [Fin.append_right]
            exact (show sortEval SortTag.rv c' from hc'0.1)
      have hv0 : Fin.append (Fin.append z u) y ∘ volIdx₀ p W.arity ∈ W.volume := by
        rw [append_volIdx₀]
        exact hc
      have hPy : Fin.append (Fin.append z u) y ∘ Fin.natAdd (p + W.arity) ∈ {z | Proper z} := by
        rw [append_comp_natAdd]
        intro j
        fin_cases j
        · exact hc0
        · exact hc'0
      have hin := hsame u y ⟨⟨hv0, hsy⟩, ⟨hPy, hsy⟩⟩
      rcases hin with ⟨⟨hv1, -⟩, ⟨⟨-, he⟩, -⟩⟩ | ⟨⟨-, hv1⟩, ⟨-, he⟩⟩
      · rw [append_volIdx₁] at hv1
        refine ⟨fun _ => by simpa [y] using he, fun _ => hv1⟩
      · constructor
        · intro h
          exact absurd (show _ ∈ _ ∧ _ from ⟨by rw [append_volIdx₁]; exact h, hsy⟩) hv1
        · intro h
          refine absurd ⟨?_, hsy⟩ he
          rw [W.append_swap_codes z u y]
          refine ⟨fun j => ?_, by simpa [y] using h⟩
          fin_cases j
          · exact hc'0
          · exact hc0
    · obtain ⟨-, hP, hall⟩ := hbz
      refine ⟨codeValue (b 0), codeValue (b 1), fun u hu i hi0 => ?_⟩
      have hu' : Fin.append (Fin.append z b ∘ Fin.castAdd 2) u ∈ W.domain := by
        rw [append_comp_castAdd]
        exact hu
      simpa using hall u hu' i hi0

end ValidDefinable

end ChartSchema

end DiamondIntegral.Section7.Lemma714Schema

/-! ### Isomorphism schemata -/

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag} {d : ℕ}

/-- A uniform family of graphs of isomorphisms between the rows of two chart
schemata. -/
structure IsoSchema (X Y : ChartSchema B sp d) where
  graph : Set (Fin ((p + X.arity) + Y.arity) → M)
  graph_definable : DefinableOverBase B (Fin.append (Fin.append sp (rvs X.arity)) (rvs Y.arity)) graph

namespace IsoSchema
variable {X Y : ChartSchema B sp d} (Φ : IsoSchema X Y)

/-- The graph row at `z`. -/
def graphRow (z : Fin p → M) (u : Fin X.arity → M) (v : Fin Y.arity → M) : Prop :=
  Fin.append (Fin.append z u) v ∈ Φ.graph

/-- Corrected weights are preserved along the graph row. -/
def WeightCond (z : Fin p → M) : Prop :=
  ∀ (u : Fin X.arity → M) (v : Fin Y.arity → M) (y y' : Fin d → M) (c c' : M),
    Φ.graphRow z u v → X.coordRow z u y → Y.coordRow z v y' → X.volRow z u c → Y.volRow z v c' →
    Proper y → Proper y' → NonzeroRV c → NonzeroRV c' →
    codeValue c * ∏ i, codeValue (y i) = codeValue c' * ∏ i, codeValue (y' i)

/-- The graph row at `z` is a measured isomorphism of the rows. -/
structure Valid (z : Fin p → M) : Prop where
  bij : bijectiveMapRowValid sp (rvs Y.arity) X.domain Y.domain Φ.graph z
  weight : Φ.WeightCond z

/-! #### The flat row layout `(u, v, y, y', c, c')` -/

/-- Length of the flat row. -/
abbrev flatLen (a b d : ℕ) : ℕ := a + (b + (d + (d + 2)))

/-- The flat row. -/
def flatRow {a b : ℕ} (u : Fin a → M) (v : Fin b → M) (y y' : Fin d → M) (c c' : M) :
    Fin (flatLen a b d) → M :=
  Fin.append u (Fin.append v (Fin.append y (Fin.append y' ![c, c'])))

section Index
variable (p a b d : ℕ)
def iz : Fin p → Fin (p + flatLen a b d) := Fin.castAdd _
def iu : Fin a → Fin (p + flatLen a b d) := fun i => Fin.natAdd p (Fin.castAdd _ i)
def iv : Fin b → Fin (p + flatLen a b d) := fun j => Fin.natAdd p (Fin.natAdd a (Fin.castAdd _ j))
def iy : Fin d → Fin (p + flatLen a b d) :=
  fun j => Fin.natAdd p (Fin.natAdd a (Fin.natAdd b (Fin.castAdd _ j)))
def iy' : Fin d → Fin (p + flatLen a b d) :=
  fun j => Fin.natAdd p (Fin.natAdd a (Fin.natAdd b (Fin.natAdd d (Fin.castAdd 2 j))))
def ic : Fin (p + flatLen a b d) := Fin.natAdd p (Fin.natAdd a (Fin.natAdd b (Fin.natAdd d (Fin.natAdd d 0))))
def ic' : Fin (p + flatLen a b d) := Fin.natAdd p (Fin.natAdd a (Fin.natAdd b (Fin.natAdd d (Fin.natAdd d 1))))
def iG : Fin ((p + a) + b) → Fin (p + flatLen a b d) := Fin.append (Fin.append (iz p a b d) (iu p a b d)) (iv p a b d)
def iXC : Fin ((p + a) + d) → Fin (p + flatLen a b d) := Fin.append (Fin.append (iz p a b d) (iu p a b d)) (iy p a b d)
def iYC : Fin ((p + b) + d) → Fin (p + flatLen a b d) := Fin.append (Fin.append (iz p a b d) (iv p a b d)) (iy' p a b d)
def iXV : Fin ((p + a) + 1) → Fin (p + flatLen a b d) :=
  Fin.append (Fin.append (iz p a b d) (iu p a b d)) (fun _ => ic p a b d)
def iYV : Fin ((p + b) + 1) → Fin (p + flatLen a b d) :=
  Fin.append (Fin.append (iz p a b d) (iv p a b d)) (fun _ => ic' p a b d)
def iW : Fin ((d + d) + 2) → Fin (p + flatLen a b d) :=
  Fin.append (Fin.append (iy p a b d) (iy' p a b d)) ![ic p a b d, ic' p a b d]
end Index

section FlatValues
variable {a b : ℕ} (z : Fin p → M) (u : Fin a → M) (v : Fin b → M) (y y' : Fin d → M) (c c' : M)

omit hM in
theorem flat_iG : Fin.append z (flatRow u v y y' c c') ∘ iG p a b d = Fin.append (Fin.append z u) v := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [iG, iz, iu, flatRow]
  · simp [iG, iv, flatRow]

omit hM in
theorem flat_iXC : Fin.append z (flatRow u v y y' c c') ∘ iXC p a b d = Fin.append (Fin.append z u) y := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [iXC, iz, iu, flatRow]
  · simp [iXC, iy, flatRow]

omit hM in
theorem flat_iYC : Fin.append z (flatRow u v y y' c c') ∘ iYC p a b d = Fin.append (Fin.append z v) y' := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [iYC, iz, iv, flatRow]
  · simp [iYC, iy', flatRow]

omit hM in
theorem flat_iXV : Fin.append z (flatRow u v y y' c c') ∘ iXV p a b d =
    Fin.append (Fin.append z u) (fun _ : Fin 1 => c) := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [iXV, iz, iu, flatRow]
  · simp [iXV, ic, flatRow]

omit hM in
theorem flat_iYV : Fin.append z (flatRow u v y y' c c') ∘ iYV p a b d =
    Fin.append (Fin.append z v) (fun _ : Fin 1 => c') := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;> simp [iYV, iz, iv, flatRow]
  · simp [iYV, ic', flatRow]

omit hM in
theorem flat_iW : Fin.append z (flatRow u v y y' c c') ∘ iW p a b d = Fin.append (Fin.append y y') ![c, c'] := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · simp only [iW, iy, Function.comp_apply, Fin.append_left, Fin.append_right, flatRow]
    · simp only [iW, iy', Function.comp_apply, Fin.append_left, Fin.append_right, flatRow]
  · fin_cases l <;> simp [iW, ic, ic', flatRow]

end FlatValues

omit hM in
theorem flatRow_decomp {a b : ℕ} (r : Fin (flatLen a b d) → M) :
    r = flatRow (fun i => r (Fin.castAdd _ i)) (fun j => r (Fin.natAdd a (Fin.castAdd _ j)))
      (fun j => r (Fin.natAdd a (Fin.natAdd b (Fin.castAdd _ j))))
      (fun j => r (Fin.natAdd a (Fin.natAdd b (Fin.natAdd d (Fin.castAdd 2 j)))))
      (r (Fin.natAdd a (Fin.natAdd b (Fin.natAdd d (Fin.natAdd d 0)))))
      (r (Fin.natAdd a (Fin.natAdd b (Fin.natAdd d (Fin.natAdd d 1))))) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp [flatRow]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp [flatRow]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp [flatRow]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp [flatRow]
  fin_cases j <;> simp [flatRow]

omit hM in
theorem flatRow_rv {a b : ℕ} {u : Fin a → M} {v : Fin b → M} {y y' : Fin d → M} {c c' : M}
    (hu : ∀ i, sortEval SortTag.rv (u i)) (hv : ∀ i, sortEval SortTag.rv (v i))
    (hy : ∀ i, sortEval SortTag.rv (y i)) (hy' : ∀ i, sortEval SortTag.rv (y' i))
    (hc : sortEval SortTag.rv c) (hc' : sortEval SortTag.rv c') :
    ∀ j, sortEval SortTag.rv (flatRow u v y y' c c' j) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · rw [flatRow, Fin.append_left]; exact hu i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · rw [flatRow, Fin.append_right, Fin.append_left]; exact hv i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · rw [flatRow, Fin.append_right, Fin.append_right, Fin.append_left]; exact hy i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · rw [flatRow, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_left]; exact hy' i
  rw [flatRow, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right]
  fin_cases j
  · exact hc
  · exact hc'

/-- The set of code tuples `(y, y', c, c')` with equal corrected weights. -/
def weightEqSet (d : ℕ) : Set (Fin ((d + d) + 2) → M) :=
  {g | Proper g ∧ codeValue (g (Fin.natAdd (d + d) 0)) * ∏ i, codeValue (g (Fin.castAdd 2 (Fin.castAdd d i))) =
    codeValue (g (Fin.natAdd (d + d) 1)) * ∏ i, codeValue (g (Fin.castAdd 2 (Fin.natAdd d i)))}

theorem weightEqSet_definable (d : ℕ) :
    DefinableOverBase B (fun _ : Fin ((d + d) + 2) => .rv) (weightEqSet (M := M) d) := by
  open GammaDefinableMaps GammaWeightProfiles in
  have h1 : MapDefinable B (fun x : Fin ((d + d) + 2) → Values.Gamma (M := M) =>
      x (Fin.natAdd (d + d) 0) * ∏ i, x (Fin.castAdd 2 (Fin.castAdd d i))) :=
    mul_definable B _ _ (projection_definable B _)
      (finset_prod_definable B Finset.univ _ (fun i _ => projection_definable B _))
  open GammaDefinableMaps GammaWeightProfiles in
  have h2 : MapDefinable B (fun x : Fin ((d + d) + 2) → Values.Gamma (M := M) =>
      x (Fin.natAdd (d + d) 1) * ∏ i, x (Fin.castAdd 2 (Fin.natAdd d i))) :=
    mul_definable B _ _ (projection_definable B _)
      (finset_prod_definable B Finset.univ _ (fun i _ => projection_definable B _))
  exact GammaDefinableMaps.equal_maps_definable B _ _ h1 h2

theorem weightEqSet_iff (y y' : Fin d → M) (c c' : M) :
    Fin.append (Fin.append y y') ![c, c'] ∈ weightEqSet d ↔
      Proper (Fin.append (Fin.append y y') ![c, c']) ∧
        codeValue c * ∏ i, codeValue (y i) = codeValue c' * ∏ i, codeValue (y' i) := by
  simp only [weightEqSet, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]
  rfl

theorem proper_flat_iff (y y' : Fin d → M) (c c' : M) :
    Proper (Fin.append (Fin.append y y') ![c, c']) ↔ Proper y ∧ Proper y' ∧ NonzeroRV c ∧ NonzeroRV c' := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
    · have := h (Fin.castAdd 2 (Fin.castAdd d i))
      rwa [Fin.append_left, Fin.append_left] at this
    · have := h (Fin.castAdd 2 (Fin.natAdd d i))
      rwa [Fin.append_left, Fin.append_right] at this
    · have := h (Fin.natAdd (d + d) 0)
      rw [Fin.append_right] at this
      exact this
    · have := h (Fin.natAdd (d + d) 1)
      rw [Fin.append_right] at this
      exact this
  · rintro ⟨hy, hy', hc, hc'⟩ j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · rw [Fin.append_left, Fin.append_left]
        exact hy i
      · rw [Fin.append_left, Fin.append_right]
        exact hy' i
    · rw [Fin.append_right]
      fin_cases l
      · exact hc
      · exact hc'

theorem weightCond_definable :
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧ Φ.WeightCond z} := by
  let a := X.arity
  let b := Y.arity
  let st := Fin.append sp (rvs (flatLen a b d))
  have hG := Φ.graph_definable.preimage_real st (iG p a b d)
  have hXC := X.coord_definable.preimage_real st (iXC p a b d)
  have hYC := Y.coord_definable.preimage_real st (iYC p a b d)
  have hXV := X.volume_definable.preimage_real st (iXV p a b d)
  have hYV := Y.volume_definable.preimage_real st (iYV p a b d)
  have hP := (GammaOrderLogic.proper_definable_base B ((d + d) + 2)).preimage_real st (iW p a b d)
  have hW := (weightEqSet_definable (M := M) (B := B) d).preimage_real st (iW p a b d)
  have h := gamma_family_row_subset_definable sp (rvs (flatLen a b d))
    (hG.inter (hXC.inter (hYC.inter (hXV.inter (hYV.inter hP))))) hW
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hz, hw⟩
    refine ⟨hz, fun r hr => ?_⟩
    obtain ⟨⟨h1, hs⟩, ⟨h2, -⟩, ⟨h3, -⟩, ⟨h4, -⟩, ⟨h5, -⟩, ⟨h6, -⟩⟩ := hr
    refine ⟨?_, hs⟩
    rw [flatRow_decomp r] at h1 h2 h3 h4 h5 h6 ⊢
    rw [flat_iG] at h1
    rw [flat_iXC] at h2
    rw [flat_iYC] at h3
    rw [flat_iXV] at h4
    rw [flat_iYV] at h5
    rw [flat_iW, proper_flat_iff] at h6
    rw [flat_iW, weightEqSet_iff, proper_flat_iff]
    exact ⟨h6, hw _ _ _ _ _ _ h1 h2 h3 h4 h5 h6.1 h6.2.1 h6.2.2.1 h6.2.2.2⟩
  · rintro ⟨hz, hw⟩
    refine ⟨hz, fun u v y y' c c' h1 h2 h3 h4 h5 hy hy' hc hc' => ?_⟩
    have hu := (mem_rows_sorted sp (rvs a) (rvs b) Φ.graph_definable h1).1
    have hv := (mem_rows_sorted sp (rvs a) (rvs b) Φ.graph_definable h1).2
    have hsr : Fin.append z (flatRow u v y y' c c') ∈ sortedUniverse st :=
      sorted_append hz (flatRow_rv hu hv (fun j => (hy j).1) (fun j => (hy' j).1) hc.1 hc'.1)
    have g1 : Fin.append z (flatRow u v y y' c c') ∘ iG p a b d ∈ Φ.graph := by rw [flat_iG]; exact h1
    have g2 : Fin.append z (flatRow u v y y' c c') ∘ iXC p a b d ∈ X.coord := by rw [flat_iXC]; exact h2
    have g3 : Fin.append z (flatRow u v y y' c c') ∘ iYC p a b d ∈ Y.coord := by rw [flat_iYC]; exact h3
    have g4 : Fin.append z (flatRow u v y y' c c') ∘ iXV p a b d ∈ X.volume := by rw [flat_iXV]; exact h4
    have g5 : Fin.append z (flatRow u v y y' c c') ∘ iYV p a b d ∈ Y.volume := by rw [flat_iYV]; exact h5
    have g6 : Proper (Fin.append z (flatRow u v y y' c c') ∘ iW p a b d) := by
      rw [flat_iW, proper_flat_iff]
      exact ⟨hy, hy', hc, hc'⟩
    have hC := (hw _ ⟨⟨g1, hsr⟩, ⟨g2, hsr⟩, ⟨g3, hsr⟩, ⟨g4, hsr⟩, ⟨g5, hsr⟩, g6, hsr⟩).1
    rw [flat_iW, weightEqSet_iff] at hC
    exact hC.2

/-- The validity locus of an isomorphism schema is definable. -/
theorem valid_definable : DefinableOverBase B sp {z | Φ.Valid z} := by
  have h1 := gamma_bijection_validity_definable sp (rvs X.arity) (rvs Y.arity)
    X.domain_definable Y.domain_definable Φ.graph_definable
  convert h1.inter Φ.weightCond_definable using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.bij, h.bij.1.1, h.weight⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-! #### The isomorphism of a valid row -/

section Realize
variable {Φ} {z : Fin p → M}

theorem Valid.map_exists (hΦ : Φ.Valid z) {u : Fin X.arity → M} (hu : u ∈ X.row z) :
    ∃! v, Φ.graphRow z u v := hΦ.bij.1.2.1 u hu

theorem Valid.source_mem (hΦ : Φ.Valid z) {u : Fin X.arity → M} {v : Fin Y.arity → M}
    (h : Φ.graphRow z u v) : u ∈ X.row z := hΦ.bij.1.2.2.1 u v h

theorem Valid.target_mem (hΦ : Φ.Valid z) {u : Fin X.arity → M} {v : Fin Y.arity → M}
    (h : Φ.graphRow z u v) : v ∈ Y.row z := (hΦ.bij.2 v).mpr ⟨u, h⟩

theorem Valid.surj (hΦ : Φ.Valid z) {v : Fin Y.arity → M} (hv : v ∈ Y.row z) :
    ∃ u, Φ.graphRow z u v := (hΦ.bij.2 v).mp hv

theorem Valid.inj (hΦ : Φ.Valid z) {u u' : Fin X.arity → M} {v : Fin Y.arity → M}
    (h : Φ.graphRow z u v) (h' : Φ.graphRow z u' v) : u = u' := by
  have hv := (mem_rows_sorted sp (rvs X.arity) (rvs Y.arity) Φ.graph_definable h).2
  obtain ⟨hfin, hle⟩ := hΦ.bij.1.2.2.2 v hv
  exact (Set.ncard_le_one_iff hfin).mp hle h h'

/-- The underlying function of the isomorphism of a valid row. -/
def isoFun (hΦ : Φ.Valid z) (u : X.row z) : Y.row z :=
  ⟨(hΦ.map_exists u.2).exists.choose, hΦ.target_mem (hΦ.map_exists u.2).exists.choose_spec⟩

theorem isoFun_graph (hΦ : Φ.Valid z) (u : X.row z) : Φ.graphRow z u.val (isoFun hΦ u).val :=
  (hΦ.map_exists u.2).exists.choose_spec

theorem isoFun_eq (hΦ : Φ.Valid z) (u : X.row z) {v : Fin Y.arity → M} (h : Φ.graphRow z u.val v) :
    (isoFun hΦ u).val = v :=
  (hΦ.map_exists u.2).unique (isoFun_graph hΦ u) h

theorem isoFun_bijective (hΦ : Φ.Valid z) : Function.Bijective (isoFun hΦ) := by
  constructor
  · intro u u' he
    apply Subtype.ext
    have h := isoFun_graph hΦ u
    rw [he] at h
    exact hΦ.inj h (isoFun_graph hΦ u')
  · intro v
    obtain ⟨u, hu⟩ := hΦ.surj v.2
    exact ⟨⟨u, hΦ.source_mem hu⟩, Subtype.ext (isoFun_eq hΦ _ hu)⟩

theorem graph_join_definable (hΦ : Φ.Valid z) :
    DefinableOverBase (baseAt B z) (fun _ : Fin (Y.arity + X.arity) => .rv)
      {w | ∃ u : X.row z, w = join Y.arity X.arity u.val (isoFun hΦ u).val} := by
  have h := (row2_definable sp (rvs X.arity) (rvs Y.arity) Φ.graph_definable z).preimage_real
    (fun _ : Fin (Y.arity + X.arity) => .rv) (ChartSchema.graphIndex X.arity Y.arity)
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, ChartSchema.graphIndex, Function.comp_def, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨u, rfl⟩
    have hg := isoFun_graph hΦ u
    refine ⟨?_, ?_⟩
    · simp only [join_head, join_tail]
      exact hg
    · have hs := mem_rows_sorted sp (rvs X.arity) (rvs Y.arity) Φ.graph_definable hg
      apply GammaBoundedProducts.all_coordinates Y.arity X.arity (fun x => sortEval SortTag.rv x)
      · intro i; rw [join_head]; exact hs.1 i
      · intro i; rw [join_tail]; exact hs.2 i
  · rintro ⟨hg, -⟩
    have hu := hΦ.source_mem hg
    refine ⟨⟨_, hu⟩, ?_⟩
    rw [isoFun_eq hΦ ⟨_, hu⟩ hg]
    exact (join_reconstruct Y.arity X.arity w).symm

theorem weight_eq_of_valid (hX : X.Valid z) (hY : Y.Valid z) (hΦ : Φ.Valid z) (u : X.row z) :
    (X.toChart z hX).correctedWeight u.val = (Y.toChart z hY).correctedWeight (isoFun hΦ u).val := by
  obtain ⟨c, hc⟩ := hX.vol_total u.val u.2
  obtain ⟨c', hc'⟩ := hY.vol_total _ (isoFun hΦ u).2
  have hcv := (ChartSchema.volRow_iff hX _ c).mp hc
  have hcv' := (ChartSchema.volRow_iff hY _ c').mp hc'
  have h := hΦ.weight u.val (isoFun hΦ u).val (X.coordAt z u.val) (Y.coordAt z (isoFun hΦ u).val) c c'
    (isoFun_graph hΦ u) (ChartSchema.coordRow_coordAt hX u.2) (ChartSchema.coordRow_coordAt hY (isoFun hΦ u).2)
    hc hc' (ChartSchema.coordAt_proper hX u.2) (ChartSchema.coordAt_proper hY (isoFun hΦ u).2) hcv.2.1 hcv'.2.1
  change X.volAt z u.val * _ = Y.volAt z (isoFun hΦ u).val * _
  rw [← hcv.2.2, ← hcv'.2.2]
  exact h

/-- **The measured isomorphism of a valid row**, over `B ∪ z`. -/
def toIso (hX : X.Valid z) (hY : Y.Valid z) (hΦ : Φ.Valid z) : Iso (X.toChart z hX) (Y.toChart z hY) where
  equiv := Equiv.ofBijective (isoFun hΦ) (isoFun_bijective hΦ)
  graph_definable := graph_join_definable hΦ
  weight_eq := weight_eq_of_valid hX hY hΦ

end Realize

end IsoSchema
end DiamondIntegral.Section7.Lemma714Schema
