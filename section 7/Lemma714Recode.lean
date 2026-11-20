import «section 7».Lemma714Cover

/-! Lemma 7.14, part 10: recoding schemata along a key relation.

Freezing (Step 2 of the proof) yields RV keys `x` and a `B`-definable relation
`K(x, z)` between keys and original parameters (the frozen centres of the points
with key `x`). On each key class the rows of the witness data are constant.
Recoding replaces the original parameter by the key:
`D♯ = {(x, v) | ∃ z, K(x, z) ∧ (z, v) ∈ D}`.
Where the rows of `D` are constant on the `K`-class of `x`, the row of `D♯` at `x`
is the row of `D` at any `z` with `K(x, z)` (`recodeSet_row`).

Validity of every kind of schema depends only on its rows. So a schema whose
rows are constant on key classes is, after recoding, valid at a key wherever it
is valid at a related parameter (`ChartSchema.recode_valid` and its analogues).
Freezing proves the constancy; the indexed realization over the keys then
descends the witness to `S`. -/

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
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

/-! ### Key relations and recoded sets -/

/-- A `B`-definable relation between new parameters (keys, sorts `sq`) and
original parameters (sorts `sp`), in the layout `(x, z)`. -/
structure KeyRel (B : Base (M := M)) (sq : Fin q → SortTag) (sp : Fin p → SortTag) where
  rel : Set (Fin (q + p) → M)
  rel_definable : DefinableOverBase B (Fin.append sq sp) rel

namespace KeyRel
variable (K : KeyRel B sq sp)

/-- `K(x, z)`. -/
def R (x : Fin q → M) (z : Fin p → M) : Prop := Fin.append x z ∈ K.rel

/-- Index of the new parameter `x` in the layout `(x, v, z)`. -/
def idxX (q p n : ℕ) : Fin q → Fin ((q + n) + p) := fun i => Fin.castAdd p (Fin.castAdd n i)
/-- Index of the row `v` in the layout `(x, v, z)`. -/
def idxV (q p n : ℕ) : Fin n → Fin ((q + n) + p) := fun i => Fin.castAdd p (Fin.natAdd q i)
/-- Index of the old parameter `z` in the layout `(x, v, z)`. -/
def idxZ (q p n : ℕ) : Fin p → Fin ((q + n) + p) := fun i => Fin.natAdd (q + n) i

/-- The recoding of a set `D ⊆ M^(p + n)` along `K`. -/
def recodeSet {n : ℕ} (D : Set (Fin (p + n) → M)) : Set (Fin (q + n) → M) :=
  {w | ∃ z : Fin p → M, Fin.append w z ∈
    ({u | u ∘ Fin.append (idxX q p n) (idxZ q p n) ∈ K.rel ∧ u ∈ sortedUniverse (Fin.append (Fin.append sq (rvs n)) sp)} ∩
      {u | u ∘ Fin.append (idxZ q p n) (idxV q p n) ∈ D ∧ u ∈ sortedUniverse (Fin.append (Fin.append sq (rvs n)) sp)})}

theorem recodeSet_definable {n : ℕ} {D : Set (Fin (p + n) → M)} (hD : DefinableOverBase B (Fin.append sp (rvs n)) D) :
    DefinableOverBase B (Fin.append sq (rvs n)) (K.recodeSet D) :=
  gamma_family_row_exists_definable _ sp ((K.rel_definable.preimage_real _ _).inter (hD.preimage_real _ _))

omit hM in
theorem comp_idxXZ {n : ℕ} (x : Fin q → M) (v : Fin n → M) (z : Fin p → M) :
    Fin.append (Fin.append x v) z ∘ Fin.append (idxX q p n) (idxZ q p n) = Fin.append x z := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [idxX, idxZ]

omit hM in
theorem comp_idxZV {n : ℕ} (x : Fin q → M) (v : Fin n → M) (z : Fin p → M) :
    Fin.append (Fin.append x v) z ∘ Fin.append (idxZ q p n) (idxV q p n) = Fin.append z v := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [idxV, idxZ]

/-- The rows of `D` are constant on the `K`-class of `x`. -/
def RowConst {n : ℕ} (D : Set (Fin (p + n) → M)) (x : Fin q → M) : Prop :=
  ∀ z z', K.R x z → K.R x z' → ∀ v : Fin n → M, Fin.append z v ∈ D ↔ Fin.append z' v ∈ D

/-- **Rows of a recoded set.** -/
theorem recodeSet_row {n : ℕ} {D : Set (Fin (p + n) → M)} (hD : DefinableOverBase B (Fin.append sp (rvs n)) D)
    {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i)) (hz : ∀ i, sortEval (sp i) (z i))
    (hK : K.R x z) (hc : K.RowConst D x) (v : Fin n → M) :
    Fin.append x v ∈ K.recodeSet D ↔ Fin.append z v ∈ D := by
  constructor
  · rintro ⟨z', ⟨h1, -⟩, ⟨h2, -⟩⟩
    rw [comp_idxXZ] at h1
    rw [comp_idxZV] at h2
    exact (hc z' z h1 hK v).mp h2
  · intro h
    have hv : ∀ i, sortEval (rvs n i) (v i) := by
      intro i
      have := hD.proper _ h (Fin.natAdd p i)
      rwa [Fin.append_right, Fin.append_right] at this
    have hs := sorted_append (sorted_append hx hv) hz
    refine ⟨z, ⟨?_, hs⟩, ⟨?_, hs⟩⟩
    · rw [comp_idxXZ]; exact hK
    · rw [comp_idxZV]; exact h

section TwoBlock
variable {n m : ℕ}

/-- Indices in the layout `(x, u, y, z)`. -/
def idx2X (q p n m : ℕ) : Fin q → Fin (((q + n) + m) + p) := fun i => Fin.castAdd p (Fin.castAdd m (Fin.castAdd n i))
def idx2U (q p n m : ℕ) : Fin n → Fin (((q + n) + m) + p) := fun i => Fin.castAdd p (Fin.castAdd m (Fin.natAdd q i))
def idx2Y (q p n m : ℕ) : Fin m → Fin (((q + n) + m) + p) := fun i => Fin.castAdd p (Fin.natAdd (q + n) i)
def idx2Z (q p n m : ℕ) : Fin p → Fin (((q + n) + m) + p) := fun i => Fin.natAdd ((q + n) + m) i

/-- Recoding of a two-block set `D ⊆ M^((p + n) + m)`. -/
def recodeSet2 (D : Set (Fin ((p + n) + m) → M)) : Set (Fin ((q + n) + m) → M) :=
  {w | ∃ z : Fin p → M, Fin.append w z ∈
    ({v | v ∘ Fin.append (idx2X q p n m) (idx2Z q p n m) ∈ K.rel ∧
        v ∈ sortedUniverse (Fin.append (Fin.append (Fin.append sq (rvs n)) (rvs m)) sp)} ∩
      {v | v ∘ Fin.append (Fin.append (idx2Z q p n m) (idx2U q p n m)) (idx2Y q p n m) ∈ D ∧
        v ∈ sortedUniverse (Fin.append (Fin.append (Fin.append sq (rvs n)) (rvs m)) sp)})}

theorem recodeSet2_definable {D : Set (Fin ((p + n) + m) → M)}
    (hD : DefinableOverBase B (Fin.append (Fin.append sp (rvs n)) (rvs m)) D) :
    DefinableOverBase B (Fin.append (Fin.append sq (rvs n)) (rvs m)) (K.recodeSet2 D) :=
  gamma_family_row_exists_definable _ sp ((K.rel_definable.preimage_real _ _).inter (hD.preimage_real _ _))

omit hM in
theorem comp_idx2XZ (x : Fin q → M) (u : Fin n → M) (y : Fin m → M) (z : Fin p → M) :
    Fin.append (Fin.append (Fin.append x u) y) z ∘ Fin.append (idx2X q p n m) (idx2Z q p n m) = Fin.append x z := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [idx2X, idx2Z]

omit hM in
theorem comp_idx2ZUY (x : Fin q → M) (u : Fin n → M) (y : Fin m → M) (z : Fin p → M) :
    Fin.append (Fin.append (Fin.append x u) y) z ∘ Fin.append (Fin.append (idx2Z q p n m) (idx2U q p n m))
      (idx2Y q p n m) = Fin.append (Fin.append z u) y := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [idx2Z, idx2U]
  · simp [idx2Y]

/-- Constancy of rows of a two-block set. -/
def RowConst2 (D : Set (Fin ((p + n) + m) → M)) (x : Fin q → M) : Prop :=
  ∀ z z', K.R x z → K.R x z' → ∀ (u : Fin n → M) (y : Fin m → M),
    Fin.append (Fin.append z u) y ∈ D ↔ Fin.append (Fin.append z' u) y ∈ D

/-- **Rows of a recoded two-block set.** -/
theorem recodeSet2_row {D : Set (Fin ((p + n) + m) → M)}
    (hD : DefinableOverBase B (Fin.append (Fin.append sp (rvs n)) (rvs m)) D)
    {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i)) (hz : ∀ i, sortEval (sp i) (z i))
    (hK : K.R x z) (hc : K.RowConst2 D x) (u : Fin n → M) (y : Fin m → M) :
    Fin.append (Fin.append x u) y ∈ K.recodeSet2 D ↔ Fin.append (Fin.append z u) y ∈ D := by
  constructor
  · rintro ⟨z', ⟨h1, -⟩, ⟨h2, -⟩⟩
    rw [comp_idx2XZ] at h1
    rw [comp_idx2ZUY] at h2
    exact (hc z' z h1 hK u y).mp h2
  · intro h
    have hs := mem_rows_sorted sp (rvs n) (rvs m) hD h
    have hss := sorted_append (sorted_append (sorted_append hx hs.1) hs.2) hz
    refine ⟨z, ⟨?_, hss⟩, ⟨?_, hss⟩⟩
    · rw [comp_idx2XZ]; exact hK
    · rw [comp_idx2ZUY]; exact h

end TwoBlock

end KeyRel

/-! ### Recoding chart schemata -/

namespace ChartSchema
variable {d : ℕ} (K : KeyRel B sq sp) (W : ChartSchema B sp d)

/-- The recoding of a chart schema along `K`. -/
def recode : ChartSchema B sq d where
  arity := W.arity
  domain := K.recodeSet W.domain
  domain_definable := K.recodeSet_definable W.domain_definable
  coord := K.recodeSet2 W.coord
  coord_definable := K.recodeSet2_definable W.coord_definable
  volume := K.recodeSet2 W.volume
  volume_definable := K.recodeSet2_definable W.volume_definable
  bound := W.bound

/-- The rows of `W` are constant on the `K`-class of `x`. -/
def RowConst (x : Fin q → M) : Prop :=
  K.RowConst W.domain x ∧ K.RowConst2 W.coord x ∧ K.RowConst2 W.volume x

variable {K W} {x : Fin q → M} {z : Fin p → M} (hx : ∀ i, sortEval (sq i) (x i))
  (hz : ∀ i, sortEval (sp i) (z i)) (hK : K.R x z) (hc : W.RowConst K x)
include hx hz hK hc

theorem recode_row (u : Fin W.arity → M) : u ∈ (W.recode K).row x ↔ u ∈ W.row z :=
  K.recodeSet_row W.domain_definable hx hz hK hc.1 u

theorem recode_coordRow (u : Fin W.arity → M) (y : Fin d → M) :
    (W.recode K).coordRow x u y ↔ W.coordRow z u y :=
  K.recodeSet2_row W.coord_definable hx hz hK hc.2.1 u y

theorem recode_volRow (u : Fin W.arity → M) (c : M) :
    (W.recode K).volRow x u c ↔ W.volRow z u c :=
  K.recodeSet2_row W.volume_definable hx hz hK hc.2.2 u _

/-- **Validity passes to the recoding** at keys with constant rows. -/
theorem recode_valid (hW : W.Valid z) : (W.recode K).Valid x := by
  have hr := recode_row hx hz hK hc
  have hco := recode_coordRow hx hz hK hc
  have hv := recode_volRow hx hz hK hc
  refine ⟨⟨hx, fun u hu => ?_, fun u y h => ?_, fun y hy => ?_⟩, fun u y h => ?_, fun u hu => ?_,
    fun u c h => ?_, fun u c c' h h0 h0' => ?_, ?_⟩
  · obtain ⟨y, hy, huniq⟩ := hW.map.2.1 u ((hr u).mp hu)
    exact ⟨y, (hco u y).mpr hy, fun y' h' => huniq y' ((hco u y').mp h')⟩
  · exact (hr u).mpr (hW.map.2.2.1 u y ((hco u y).mp h))
  · obtain ⟨hf, hle⟩ := hW.map.2.2.2 y hy
    have hsub : {u : Fin (W.recode K).arity → M | Fin.append (Fin.append x u) y ∈ (W.recode K).coord} ⊆
        {u | Fin.append (Fin.append z u) y ∈ W.coord} := fun u hu => (hco u y).mp hu
    exact ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans hle⟩
  · exact hW.proper u y ((hco u y).mp h)
  · obtain ⟨c, hc'⟩ := hW.vol_total u ((hr u).mp hu)
    exact ⟨c, (hv u c).mpr hc'⟩
  · obtain ⟨h1, h2⟩ := hW.vol_dom u c ((hv u c).mp h)
    exact ⟨(hr u).mpr h1, h2⟩
  · rw [hv u c']
    exact hW.vol_same u c c' ((hv u c).mp h) h0 h0'
  · obtain ⟨lo, hi, hb⟩ := hW.bounded
    exact ⟨lo, hi, fun u hu => hb u ((hr u).mp hu)⟩

end ChartSchema

end DiamondIntegral.Section7.Lemma714Schema
