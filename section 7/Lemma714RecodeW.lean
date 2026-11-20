import «section 7».Lemma714Descent

/-! Lemma 7.14, part 21: recoding witness schemata along key relations.

After freezing, a witness schema valid at a frozen point `z` is moved to the
key `x` (with `K(x, z)`) by recoding every set of the witness
(`MoveSchema.recode`, `ChainSchema.recode`, `WitnessSchema.recode`). Where all
rows are constant on the `K`-class of `x` (`RowConst`), the recoded witness is
valid at `x` (`WitnessSchema.recode_valid`).

The isomorphism schemata of a move have derived sources and targets
(restrictions, shell and endpoint). Their validity is a statement about rows
only (`RawIso`), and it transfers from `z` to `x` along equivalences of rows
(`RawIso.transfer`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

/-! ### Raw isomorphism rows -/

/-- Validity of an isomorphism schema, as a statement about raw rows. -/
def RawIso {n : ℕ} (s : Fin n → SortTag) {a b d : ℕ} (DX : Set (Fin (n + a) → M)) (DY : Set (Fin (n + b) → M))
    (CX : Set (Fin ((n + a) + d) → M)) (CY : Set (Fin ((n + b) + d) → M))
    (VX : Set (Fin ((n + a) + 1) → M)) (VY : Set (Fin ((n + b) + 1) → M))
    (G : Set (Fin ((n + a) + b) → M)) (z : Fin n → M) : Prop :=
  bijectiveMapRowValid s (rvs b) DX DY G z ∧
  ∀ (u : Fin a → M) (v : Fin b → M) (y y' : Fin d → M) (c c' : M),
    Fin.append (Fin.append z u) v ∈ G → Fin.append (Fin.append z u) y ∈ CX → Fin.append (Fin.append z v) y' ∈ CY →
    Fin.append (Fin.append z u) (fun _ : Fin 1 => c) ∈ VX → Fin.append (Fin.append z v) (fun _ : Fin 1 => c') ∈ VY →
    Proper y → Proper y' → NonzeroRV c → NonzeroRV c' →
    codeValue c * ∏ i, codeValue (y i) = codeValue c' * ∏ i, codeValue (y' i)

theorem IsoSchema.valid_iff_raw {d : ℕ} {X Y : ChartSchema B sp d} (Φ : IsoSchema X Y) (z : Fin p → M) :
    Φ.Valid z ↔ RawIso sp X.domain Y.domain X.coord Y.coord X.volume Y.volume Φ.graph z :=
  ⟨fun h => ⟨h.bij, h.weight⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Transfer of raw isomorphism rows** along equivalences of rows. -/
theorem RawIso.transfer {a b d : ℕ} {DX : Set (Fin (p + a) → M)} {DY : Set (Fin (p + b) → M)}
    {CX : Set (Fin ((p + a) + d) → M)} {CY : Set (Fin ((p + b) + d) → M)}
    {VX : Set (Fin ((p + a) + 1) → M)} {VY : Set (Fin ((p + b) + 1) → M)} {G : Set (Fin ((p + a) + b) → M)}
    {DX' : Set (Fin (q + a) → M)} {DY' : Set (Fin (q + b) → M)}
    {CX' : Set (Fin ((q + a) + d) → M)} {CY' : Set (Fin ((q + b) + d) → M)}
    {VX' : Set (Fin ((q + a) + 1) → M)} {VY' : Set (Fin ((q + b) + 1) → M)} {G' : Set (Fin ((q + a) + b) → M)}
    {z : Fin p → M} {x : Fin q → M} (hx : ∀ i, sortEval (sq i) (x i))
    (hDX : ∀ u, Fin.append x u ∈ DX' ↔ Fin.append z u ∈ DX)
    (hDY : ∀ v, Fin.append x v ∈ DY' ↔ Fin.append z v ∈ DY)
    (hCX : ∀ u y, Fin.append (Fin.append x u) y ∈ CX' ↔ Fin.append (Fin.append z u) y ∈ CX)
    (hCY : ∀ v y, Fin.append (Fin.append x v) y ∈ CY' ↔ Fin.append (Fin.append z v) y ∈ CY)
    (hVX : ∀ u c, Fin.append (Fin.append x u) (fun _ : Fin 1 => c) ∈ VX' ↔
      Fin.append (Fin.append z u) (fun _ : Fin 1 => c) ∈ VX)
    (hVY : ∀ v c, Fin.append (Fin.append x v) (fun _ : Fin 1 => c) ∈ VY' ↔
      Fin.append (Fin.append z v) (fun _ : Fin 1 => c) ∈ VY)
    (hG : ∀ u v, Fin.append (Fin.append x u) v ∈ G' ↔ Fin.append (Fin.append z u) v ∈ G)
    (h : RawIso sp DX DY CX CY VX VY G z) : RawIso sq DX' DY' CX' CY' VX' VY' G' x := by
  obtain ⟨⟨⟨_, hT, hD, hF⟩, hE⟩, hW⟩ := h
  refine ⟨⟨⟨hx, fun u hu => ?_, fun u v h => ?_, fun v hv => ?_⟩, fun v => ?_⟩, ?_⟩
  · obtain ⟨v, hv, huniq⟩ := hT u ((hDX u).mp hu)
    exact ⟨v, (hG u v).mpr hv, fun v' h' => huniq v' ((hG u v').mp h')⟩
  · exact (hDX u).mpr (hD u v ((hG u v).mp h))
  · obtain ⟨hf, hle⟩ := hF v hv
    have hsub : {u : Fin a → M | Fin.append (Fin.append x u) v ∈ G'} ⊆ {u | Fin.append (Fin.append z u) v ∈ G} :=
      fun u hu => (hG u v).mp hu
    exact ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans hle⟩
  · have := hE v
    constructor
    · intro hv
      obtain ⟨u, hu⟩ := this.mp ((hDY v).mp hv)
      exact ⟨u, (hG u v).mpr hu⟩
    · rintro ⟨u, hu⟩
      exact (hDY v).mpr (this.mpr ⟨u, (hG u v).mp hu⟩)
  · intro u v y y' c c' h1 h2 h3 h4 h5 hy hy' hc hc'
    exact hW u v y y' c c' ((hG u v).mp h1) ((hCX u y).mp h2) ((hCY v y').mp h3) ((hVX u c).mp h4)
      ((hVY v c').mp h5) hy hy' hc hc'

/-! ### Rows of recoded schemata -/

section Rows
variable (K : KeyRel B sq sp) {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i))
  (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z)

omit hM in
theorem append_sorted_iff {n : ℕ} {s : Fin n → SortTag} {w : Fin n → M} (hw : ∀ i, sortEval (s i) (w i))
    {m : ℕ} (u : Fin m → M) : Fin.append w u ∈ sortedUniverse (Fin.append s (rvs m)) ↔ ∀ j, sortEval SortTag.rv (u j) := by
  constructor
  · intro h j
    have := h (Fin.natAdd n j)
    simpa only [Fin.append_right] using this
  · intro hu j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [Fin.append_left]
      exact hw l
    · simp only [Fin.append_right]
      exact hu l

include hx hz hK in
theorem recodeSet_rowIff {n : ℕ} {P : Set (Fin (p + n) → M)} (hP : DefinableOverBase B (Fin.append sp (rvs n)) P)
    (hc : K.RowConst P x) (u : Fin n → M) : Fin.append x u ∈ K.recodeSet P ↔ Fin.append z u ∈ P :=
  K.recodeSet_row hP hx hz hK hc u

include hx hz in
theorem compl_rowIff {n : ℕ} {P : Set (Fin (p + n) → M)} {P' : Set (Fin (q + n) → M)}
    (hPP : ∀ u, Fin.append x u ∈ P' ↔ Fin.append z u ∈ P) (u : Fin n → M) :
    Fin.append x u ∈ compl (Fin.append sq (rvs n)) P' ↔ Fin.append z u ∈ compl (Fin.append sp (rvs n)) P := by
  simp only [compl, Set.mem_diff]
  rw [append_sorted_iff hx, append_sorted_iff hz, hPP]

variable {K} in
include hx hz hK in
/-- Rows of a restricted recoded chart schema. -/
theorem recode_restrict_rows {d : ℕ} {W : ChartSchema B sp d} (hW : W.RowConst K x)
    {P : Set (Fin (p + W.arity) → M)} (hP : DefinableOverBase B (Fin.append sp (rvs W.arity)) P)
    {P' : Set (Fin (q + W.arity) → M)} (hP' : DefinableOverBase B (Fin.append sq (rvs W.arity)) P')
    (hPP : ∀ u, Fin.append x u ∈ P' ↔ Fin.append z u ∈ P) :
    (∀ u, Fin.append x u ∈ ((W.recode K).restrict P' hP').domain ↔ Fin.append z u ∈ (W.restrict P hP).domain) ∧
    (∀ u y, Fin.append (Fin.append x u) y ∈ ((W.recode K).restrict P' hP').coord ↔
      Fin.append (Fin.append z u) y ∈ (W.restrict P hP).coord) ∧
    (∀ u c, Fin.append (Fin.append x u) (fun _ : Fin 1 => c) ∈ ((W.recode K).restrict P' hP').volume ↔
      Fin.append (Fin.append z u) (fun _ : Fin 1 => c) ∈ (W.restrict P hP).volume) := by
  refine ⟨fun u => ?_, fun u y => ?_, fun u c => ?_⟩
  · change Fin.append x u ∈ (W.recode K).domain ∩ P' ↔ Fin.append z u ∈ W.domain ∩ P
    rw [Set.mem_inter_iff, Set.mem_inter_iff, hPP]
    exact and_congr_left' (ChartSchema.recode_row hx hz hK hW u)
  · have h1 := ChartSchema.restrict_coordRow (W := W.recode K) (P := P') (hP := hP') x u y
    have h2 := ChartSchema.restrict_coordRow (W := W) (P := P) (hP := hP) z u y
    unfold ChartSchema.coordRow at h1 h2
    rw [h1, h2, hPP]
    exact and_congr_left' (ChartSchema.recode_coordRow hx hz hK hW u y)
  · have h1 := ChartSchema.restrict_volRow (W := W.recode K) (P := P') (hP := hP') x u c
    have h2 := ChartSchema.restrict_volRow (W := W) (P := P) (hP := hP) z u c
    unfold ChartSchema.volRow at h1 h2
    rw [h1, h2, hPP]
    exact and_congr_left' (ChartSchema.recode_volRow hx hz hK hW u c)

variable {K} in
include hx hz hK in
/-- Rows of a recoded chart schema. -/
theorem recode_rows {d : ℕ} {W : ChartSchema B sp d} (hW : W.RowConst K x) :
    (∀ u, Fin.append x u ∈ (W.recode K).domain ↔ Fin.append z u ∈ W.domain) ∧
    (∀ u y, Fin.append (Fin.append x u) y ∈ (W.recode K).coord ↔ Fin.append (Fin.append z u) y ∈ W.coord) ∧
    (∀ u c, Fin.append (Fin.append x u) (fun _ : Fin 1 => c) ∈ (W.recode K).volume ↔
      Fin.append (Fin.append z u) (fun _ : Fin 1 => c) ∈ W.volume) :=
  ⟨ChartSchema.recode_row hx hz hK hW, ChartSchema.recode_coordRow hx hz hK hW,
    ChartSchema.recode_volRow hx hz hK hW⟩

variable {K} in
include hx hz hK in
theorem recode_coordAt {d : ℕ} {W : ChartSchema B sp d} (hW : W.RowConst K x) (hv : W.Valid z)
    (hv' : (W.recode K).Valid x) {u : Fin W.arity → M} (hu : u ∈ W.row z) :
    (W.recode K).coordAt x u = W.coordAt z u := by
  have h1 := ChartSchema.coordRow_coordAt hv hu
  have hu' : u ∈ (W.recode K).row x := (ChartSchema.recode_row hx hz hK hW u).mpr hu
  have h2 := ChartSchema.coordRow_coordAt hv' hu'
  have h3 := (ChartSchema.recode_coordRow hx hz hK hW u _).mp h2
  exact ((ChartSchema.coordRow_iff hv u _).mp h3).2.symm

variable {K} in
include hx hz hK in
theorem recode_apAt {k : ℕ} {D : DatumSchema B sp k} (hD : D.RowConst K x) (hv : D.Valid z)
    (hv' : (D.recode K).Valid x) {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.row z) :
    (D.recode K).apAt x u = D.apAt z u := by
  have hu' : u ∈ (D.recode K).chart.row x := (ChartSchema.recode_row hx hz hK hD.1 u).mpr hu
  have h1 := DatumSchema.apRow_apAt hv' hu'
  have h2 := (DatumSchema.recode_apRow hx hz hK hD u _).mp h1
  exact ((DatumSchema.apRow_iff hv u _).mp h2).2.symm

variable {K} in
include hx hz hK in
/-- Rows of the shell of a recoded datum. -/
theorem recode_shell_rows {k : ℕ} {D : DatumSchema B sp k} (hD : D.RowConst K x) (hv : D.Valid z)
    (hv' : (D.recode K).Valid x) :
    (∀ v, Fin.append x v ∈ (D.recode K).shellSchema.domain ↔ Fin.append z v ∈ D.shellSchema.domain) ∧
    (∀ v y, Fin.append (Fin.append x v) y ∈ (D.recode K).shellSchema.coord ↔
      Fin.append (Fin.append z v) y ∈ D.shellSchema.coord) ∧
    (∀ v c, Fin.append (Fin.append x v) (fun _ : Fin 1 => c) ∈ (D.recode K).shellSchema.volume ↔
      Fin.append (Fin.append z v) (fun _ : Fin 1 => c) ∈ D.shellSchema.volume) := by
  have hdom : ∀ (u : Fin D.chart.arity → M) (s0 : M),
      Fin.append x (Fin.append u (fun _ : Fin 1 => s0)) ∈ (D.recode K).shellDom ↔
        Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) ∈ D.shellDom := by
    intro u s0
    rw [DatumSchema.mem_shellDom, DatumSchema.mem_shellDom]
    have hr := ChartSchema.recode_row hx hz hK hD.1 u
    unfold ChartSchema.row at hr
    rw [show Fin.append x u ∈ (D.recode K).chart.domain ↔ Fin.append z u ∈ D.chart.domain from hr]
    simp only [DatumSchema.recode_apRow hx hz hK hD]
  have hsplit : ∀ v : Fin (D.chart.arity + 1) → M, ∃ (u : Fin D.chart.arity → M) (s0 : M),
      v = Fin.append u (fun _ : Fin 1 => s0) := fun v => ⟨_, _, DatumSchema.append_decomp_one v⟩
  refine ⟨fun v => ?_, fun v y => ?_, fun v c => ?_⟩
  · obtain ⟨u, s0, rfl⟩ := hsplit v
    exact hdom u s0
  · obtain ⟨u, s0, rfl⟩ := hsplit v
    have h1 := DatumSchema.shell_coordRow_iff hv' u s0 y
    have h2 := DatumSchema.shell_coordRow_iff hv u s0 y
    unfold ChartSchema.coordRow at h1 h2
    rw [h1, h2, hdom]
    have hc : Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) ∈ D.shellDom →
        (D.recode K).chart.coordAt x u = D.chart.coordAt z u := fun hm =>
      recode_coordAt hx hz hK hD.1 hv.chart hv'.chart ((D.mem_shellDom z _ _).mp hm).1
    constructor
    · rintro ⟨hm, rfl⟩
      refine ⟨hm, ?_⟩
      rw [hc hm]
      rfl
    · rintro ⟨hm, rfl⟩
      refine ⟨hm, ?_⟩
      rw [hc hm]
      rfl
  · obtain ⟨u, s0, rfl⟩ := hsplit v
    have h1 := DatumSchema.shell_volRow (D.recode K) x u s0 c
    have h2 := DatumSchema.shell_volRow D z u s0 c
    unfold ChartSchema.volRow at h1 h2
    rw [h1, h2, hdom]
    exact and_congr_right' (ChartSchema.recode_volRow hx hz hK hD.1 u c)

variable {K} in
include hx hz hK in
/-- Rows of the endpoint of a recoded datum. -/
theorem recode_end_rows {k : ℕ} {D : DatumSchema B sp k} (hD : D.RowConst K x) (hv : D.Valid z)
    (hv' : (D.recode K).Valid x) :
    (∀ u, Fin.append x u ∈ (D.recode K).endSchema.domain ↔ Fin.append z u ∈ D.endSchema.domain) ∧
    (∀ u y, Fin.append (Fin.append x u) y ∈ (D.recode K).endSchema.coord ↔
      Fin.append (Fin.append z u) y ∈ D.endSchema.coord) ∧
    (∀ u c, Fin.append (Fin.append x u) (fun _ : Fin 1 => c) ∈ (D.recode K).endSchema.volume ↔
      Fin.append (Fin.append z u) (fun _ : Fin 1 => c) ∈ D.endSchema.volume) := by
  refine ⟨ChartSchema.recode_row hx hz hK hD.1, fun u y => ?_, ChartSchema.recode_volRow hx hz hK hD.1⟩
  have h1 := DatumSchema.endSchema_coordRow_iff hv' u y
  have h2 := DatumSchema.endSchema_coordRow_iff hv u y
  unfold ChartSchema.coordRow at h1 h2
  rw [h1, h2]
  have hr := ChartSchema.recode_row hx hz hK hD.1 u
  have hc : ∀ u0 : Fin D.chart.arity → M, u0 ∈ D.chart.row z →
      (D.recode K).chart.coordAt x u0 = D.chart.coordAt z u0 := fun u0 hu0 =>
    recode_coordAt hx hz hK hD.1 hv.chart hv'.chart hu0
  constructor
  · rintro ⟨hu, rfl⟩
    have hu0 := hr.mp hu
    refine ⟨hu0, ?_⟩
    rw [hc u hu0, recode_apAt hx hz hK hD hv hv' hu0]
    rfl
  · rintro ⟨hu, rfl⟩
    refine ⟨hr.mpr hu, ?_⟩
    rw [hc u hu, recode_apAt hx hz hK hD hv hv' hu]
    rfl

end Rows

/-! ### Recoding moves, chains and witnesses -/

section Witness
variable (K : KeyRel B sq sp)

namespace MoveSchema
variable {k : ℕ} {X : ChartSchema B sp (1 + k)} (μ : MoveSchema X)

/-- The rows of every set of a move schema are constant on the `K`-class of `x`. -/
structure RowConst (x : Fin q → M) : Prop where
  rest : μ.rest.RowConst K x
  datum : μ.datum.RowConst K x
  result : μ.result.RowConst K x
  piece : K.RowConst μ.piece x
  q₁ : K.RowConst μ.q₁ x
  q₂ : K.RowConst μ.q₂ x
  isoRest : K.RowConst2 μ.isoRest.graph x
  isoSrc : K.RowConst2 μ.isoSrc.graph x
  isoRest' : K.RowConst2 μ.isoRest'.graph x
  isoShell : K.RowConst2 μ.isoShell.graph x
  isoEnd : K.RowConst2 μ.isoEnd.graph x

/-- **The recoding of a move schema.** -/
def recode : MoveSchema (X.recode K) where
  rest := μ.rest.recode K
  datum := μ.datum.recode K
  result := μ.result.recode K
  piece := K.recodeSet μ.piece
  piece_definable := K.recodeSet_definable μ.piece_definable
  q₁ := K.recodeSet μ.q₁
  q₁_definable := K.recodeSet_definable μ.q₁_definable
  q₂ := K.recodeSet μ.q₂
  q₂_definable := K.recodeSet_definable μ.q₂_definable
  isoRest := ⟨K.recodeSet2 μ.isoRest.graph, K.recodeSet2_definable μ.isoRest.graph_definable⟩
  isoSrc := ⟨K.recodeSet2 μ.isoSrc.graph, K.recodeSet2_definable μ.isoSrc.graph_definable⟩
  isoRest' := ⟨K.recodeSet2 μ.isoRest'.graph, K.recodeSet2_definable μ.isoRest'.graph_definable⟩
  isoShell := ⟨K.recodeSet2 μ.isoShell.graph, K.recodeSet2_definable μ.isoShell.graph_definable⟩
  isoEnd := ⟨K.recodeSet2 μ.isoEnd.graph, K.recodeSet2_definable μ.isoEnd.graph_definable⟩

variable {K μ} {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i))
  (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z)

include hx hz hK in
/-- **Validity of move schemata passes to the recoding.** -/
theorem recode_valid (hX : X.RowConst K x) (hc : μ.RowConst K x) (hμ : μ.Valid z) : (μ.recode K).Valid x := by
  have hrest := ChartSchema.recode_valid hx hz hK hc.rest hμ.rest
  have hdat := DatumSchema.recode_valid hx hz hK hc.datum hμ.datum
  have hres := ChartSchema.recode_valid hx hz hK hc.result hμ.result
  have hpiece := recodeSet_rowIff K hx hz hK μ.piece_definable hc.piece
  have hq₁ := recodeSet_rowIff K hx hz hK μ.q₁_definable hc.q₁
  have hq₂ := recodeSet_rowIff K hx hz hK μ.q₂_definable hc.q₂
  refine ⟨hrest, hdat, hres, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsoSchema.valid_iff_raw]
    obtain ⟨d1, c1, v1⟩ := recode_restrict_rows hx hz hK hX μ.piece_definable
      (K.recodeSet_definable μ.piece_definable) hpiece
    obtain ⟨d2, c2, v2⟩ := recode_rows hx hz hK hc.rest
    exact RawIso.transfer hx d1 d2 c1 c2 v1 v2
      (fun u v => K.recodeSet2_row μ.isoRest.graph_definable hx hz hK hc.isoRest u v)
      ((IsoSchema.valid_iff_raw _ _).mp hμ.isoRest)
  · rw [IsoSchema.valid_iff_raw]
    obtain ⟨d1, c1, v1⟩ := recode_restrict_rows hx hz hK hX μ.piece_definable.compl
      (K.recodeSet_definable μ.piece_definable).compl (compl_rowIff hx hz hpiece)
    obtain ⟨d2, c2, v2⟩ := recode_rows hx hz hK hc.datum.1
    exact RawIso.transfer hx d1 d2 c1 c2 v1 v2
      (fun u v => K.recodeSet2_row μ.isoSrc.graph_definable hx hz hK hc.isoSrc u v)
      ((IsoSchema.valid_iff_raw _ _).mp hμ.isoSrc)
  · rw [IsoSchema.valid_iff_raw]
    obtain ⟨d1, c1, v1⟩ := recode_restrict_rows hx hz hK hc.result μ.q₁_definable
      (K.recodeSet_definable μ.q₁_definable) hq₁
    obtain ⟨d2, c2, v2⟩ := recode_rows hx hz hK hc.rest
    exact RawIso.transfer hx d1 d2 c1 c2 v1 v2
      (fun u v => K.recodeSet2_row μ.isoRest'.graph_definable hx hz hK hc.isoRest' u v)
      ((IsoSchema.valid_iff_raw _ _).mp hμ.isoRest')
  · rw [IsoSchema.valid_iff_raw]
    have hdiff : ∀ u, Fin.append x u ∈ K.recodeSet μ.q₂ \ K.recodeSet μ.q₁ ↔ Fin.append z u ∈ μ.q₂ \ μ.q₁ := by
      intro u
      rw [Set.mem_diff, Set.mem_diff, hq₁, hq₂]
    obtain ⟨d1, c1, v1⟩ := recode_restrict_rows hx hz hK hc.result (μ.q₂_definable.sdiff μ.q₁_definable)
      ((K.recodeSet_definable μ.q₂_definable).sdiff (K.recodeSet_definable μ.q₁_definable)) hdiff
    obtain ⟨d2, c2, v2⟩ := recode_shell_rows hx hz hK hc.datum hμ.datum hdat
    exact RawIso.transfer hx d1 d2 c1 c2 v1 v2
      (fun u v => K.recodeSet2_row μ.isoShell.graph_definable hx hz hK hc.isoShell u v)
      ((IsoSchema.valid_iff_raw _ _).mp hμ.isoShell)
  · rw [IsoSchema.valid_iff_raw]
    have hunion : ∀ u, Fin.append x u ∈ K.recodeSet μ.q₁ ∪ K.recodeSet μ.q₂ ↔ Fin.append z u ∈ μ.q₁ ∪ μ.q₂ := by
      intro u
      rw [Set.mem_union, Set.mem_union, hq₁, hq₂]
    obtain ⟨d1, c1, v1⟩ := recode_restrict_rows hx hz hK hc.result (μ.q₁_definable.union μ.q₂_definable).compl
      ((K.recodeSet_definable μ.q₁_definable).union (K.recodeSet_definable μ.q₂_definable)).compl
      (compl_rowIff hx hz hunion)
    obtain ⟨d2, c2, v2⟩ := recode_end_rows hx hz hK hc.datum hμ.datum hdat
    exact RawIso.transfer hx d1 d2 c1 c2 v1 v2
      (fun u v => K.recodeSet2_row μ.isoEnd.graph_definable hx hz hK hc.isoEnd u v)
      ((IsoSchema.valid_iff_raw _ _).mp hμ.isoEnd)

end MoveSchema

namespace ChainSchema
variable {k : ℕ}

/-- The recoding of a chain schema. -/
def recode : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → ChainSchema X m → ChainSchema (X.recode K) m
  | _, _, .nil X => .nil (X.recode K)
  | _, _, .cons μ tail => .cons (μ.recode K) (recode tail)

/-- Row constancy for every move of a chain. -/
def RowConst (x : Fin q → M) : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → ChainSchema X m → Prop
  | _, _, .nil _ => True
  | _, _, .cons μ tail => μ.RowConst K x ∧ RowConst x tail

theorem last_recode : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → (c : ChainSchema X m) →
    (c.recode K).last = c.last.recode K
  | _, _, .nil _ => rfl
  | _, _, .cons _ tail => last_recode tail

variable {K} {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i))
  (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z)

include hx hz hK in
theorem recode_valid : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → (c : ChainSchema X m) →
    X.RowConst K x → c.RowConst K x → c.Valid z → (c.recode K).Valid x
  | _, _, .nil _, _, _, _ => trivial
  | _, _, .cons μ tail, hX, hc, hv =>
    ⟨MoveSchema.recode_valid hx hz hK hX hc.1 hv.1, recode_valid tail hc.1.result hc.2 hv.2⟩

end ChainSchema

theorem IsoSchema.valid_cast {d : ℕ} {X X' Y Y' : ChartSchema B sq d} (hX : X = X') (hY : Y = Y')
    (Φ : IsoSchema X Y) (x : Fin q → M) : (hY ▸ hX ▸ Φ).Valid x ↔ Φ.Valid x := by
  subst hX
  subst hY
  rfl

namespace WitnessSchema
variable {k : ℕ} {X₀ Y₀ : ChartSchema B sp (1 + k)} (W : WitnessSchema X₀ Y₀)

/-- **The recoding of a witness schema.** -/
def recode : WitnessSchema (X₀.recode K) (Y₀.recode K) where
  leftLength := W.leftLength
  rightLength := W.rightLength
  left := W.left.recode K
  right := W.right.recode K
  final := (ChainSchema.last_recode K W.right).symm ▸ (ChainSchema.last_recode K W.left).symm ▸ W.final.recode K

/-- Row constancy for every set of a witness schema. -/
structure RowConst (x : Fin q → M) : Prop where
  source : X₀.RowConst K x
  target : Y₀.RowConst K x
  left : W.left.RowConst K x
  right : W.right.RowConst K x
  final : K.RowConst2 W.final.graph x
  lastLeft : W.left.last.RowConst K x
  lastRight : W.right.last.RowConst K x

variable {K W} {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i))
  (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z)

include hx hz hK in
/-- **Validity of witness schemata passes to the recoding.** -/
theorem recode_valid (hc : W.RowConst K x) (hW : W.Valid z) : (W.recode K).Valid x := by
  refine ⟨ChartSchema.recode_valid hx hz hK hc.source hW.source,
    ChartSchema.recode_valid hx hz hK hc.target hW.target,
    ChainSchema.recode_valid hx hz hK W.left hc.source hc.left hW.left,
    ChainSchema.recode_valid hx hz hK W.right hc.target hc.right hW.right, ?_⟩
  change ((ChainSchema.last_recode K W.right).symm ▸ (ChainSchema.last_recode K W.left).symm ▸
    W.final.recode K).Valid x
  rw [IsoSchema.valid_cast]
  have hlv : W.left.last.Valid z := ChainSchema.Valid.last hW.source W.left hW.left
  have hrv : W.right.last.Valid z := ChainSchema.Valid.last hW.target W.right hW.right
  exact IsoSchema.recode_valid hx hz hK hc.lastLeft hc.lastRight hc.final hW.final

end WitnessSchema

namespace WitnessSchema0
variable {X₀ Y₀ : ChartSchema B sp 0} (W : WitnessSchema0 X₀ Y₀)

/-- The recoding of a degree-`0` witness schema. -/
def recode : WitnessSchema0 (X₀.recode K) (Y₀.recode K) := ⟨W.iso.recode K⟩

/-- Row constancy for a degree-`0` witness schema. -/
structure RowConst (x : Fin q → M) : Prop where
  source : X₀.RowConst K x
  target : Y₀.RowConst K x
  iso : K.RowConst2 W.iso.graph x

variable {K W} {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i))
  (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z)

include hx hz hK in
theorem recode_valid (hc : W.RowConst K x) (hW : W.Valid z) : (W.recode K).Valid x :=
  ⟨ChartSchema.recode_valid hx hz hK hc.source hW.source, ChartSchema.recode_valid hx hz hK hc.target hW.target,
    IsoSchema.recode_valid hx hz hK hc.source hc.target hc.iso hW.iso⟩

end WitnessSchema0

end Witness

end DiamondIntegral.Section7.Lemma714Schema
