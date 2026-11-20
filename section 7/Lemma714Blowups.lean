import «section 7».Lemma714Moves

/-! Lemma 7.14, part 4: the endpoint and shell schemata of a datum schema.

For a datum schema `D` (rows `(U, f, ω)`, coordinate `j`, aperture `τ`) the
blowup `U^{τ,j}` of Definition 7.2 is the separately tagged union of

* the endpoint `{(u, τ(u))}` with structural map `f` with `τ(u) · f_j(u)` in
  position `j` (`DatumSchema.endSchema`, rows indexed by `u`), and
* the shell `{(u, s) : 1 < vrv s ≤ vrv τ(u)}` with `s · f_j(u)` in position `j`
  (`DatumSchema.shellSchema`, rows indexed by `(u, s)`),

both with the volume of `U`. These are chart schemata built from the sets of
`D` by first-order operations, so they are `B`-definable. They are valid at
every parameter where `D` is valid; the fibre bound is the inactive bound of
`D` (`DatumSchema.Valid.endSchema`, `DatumSchema.Valid.shellSchema`).

In the witness of a blowup move the result is split into three definable
pieces, isomorphic to the rest, the shell and the endpoint (isomorphism
schemata). At the RV keys of the descent these schemata realize the Section 4
shell and endpoint charts of the descended datum. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Milestone0.Transfer

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks AnnularBlowup BlowupChart
open IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

/-! ### The blown structural map -/

section Blown
variable {k : ℕ}

omit hM in
theorem comp_join {α β : Type*} {n m : ℕ} (f : α → β) (u : Fin m → α) (y : Fin n → α) :
    f ∘ join n m u y = join n m (f ∘ u) (f ∘ y) := by
  rw [← join_reconstruct n m (f ∘ join n m u y)]
  congr 1
  · funext i; simp [join_head]
  · funext i; simp [join_tail]

/-- `y = f` with `s · f_j` in position `j`, in the layout `(f, s, y)`. -/
def blownSet (j : Fin (1 + k)) : Set (Fin (((1 + k) + 1) + (1 + k)) → M) :=
  {w | w ∈ sortedUniverse (rvs _) ∧
    (fun i => w (Fin.natAdd ((1 + k) + 1) i)) =
      Function.update (fun i => w (Fin.castAdd (1 + k) (Fin.castAdd 1 i))) j
        (iRVMul (w (Fin.castAdd (1 + k) (Fin.natAdd (1 + k) 0))) (w (Fin.castAdd (1 + k) (Fin.castAdd 1 j))))}

/-- The index map into the graph layout of `updateMap`. -/
def blownIndex (k : ℕ) : Fin ((1 + k) + (1 + (1 + k))) → Fin (((1 + k) + 1) + (1 + k)) :=
  join (1 + k) (1 + (1 + k))
    (join 1 (1 + k) (fun i => Fin.castAdd (1 + k) (Fin.castAdd 1 i)) ![Fin.castAdd (1 + k) (Fin.natAdd (1 + k) 0)])
    (fun i => Fin.natAdd ((1 + k) + 1) i)

omit hM in
theorem join_comp_head {α : Type*} {n m : ℕ} (u : Fin m → α) (y : Fin n → α) :
    join n m u y ∘ headIndex n m = u := funext (fun i => join_head n m u y i)

omit hM in
theorem join_comp_tail {α : Type*} {n m : ℕ} (u : Fin m → α) (y : Fin n → α) :
    join n m u y ∘ tailIndex n m = y := funext (fun i => join_tail n m u y i)

theorem blownSet_definable (j : Fin (1 + k)) :
    DefinableOverBase B (rvs (((1 + k) + 1) + (1 + k))) (blownSet (M := M) j) := by
  have h := (updateMap_graph_definable (M := M) B j).preimage_real (rvs (((1 + k) + 1) + (1 + k))) (blownIndex k)
  convert h using 1
  ext w
  let y0 : Fin (1 + k) → M := fun i => w (Fin.castAdd (1 + k) (Fin.castAdd 1 i))
  let s0 : M := w (Fin.castAdd (1 + k) (Fin.natAdd (1 + k) 0))
  have e1 : (w ∘ blownIndex k) ∘ headIndex (1 + k) (1 + (1 + k)) = join 1 (1 + k) y0 ![s0] := by
    rw [blownIndex, comp_join, join_comp_head, comp_join]
    congr 1
    funext l; fin_cases l; rfl
  have e2 : (w ∘ blownIndex k) ∘ tailIndex (1 + k) (1 + (1 + k)) = fun i => w (Fin.natAdd ((1 + k) + 1) i) := by
    rw [blownIndex, comp_join, join_comp_tail]
    rfl
  change (w ∈ sortedUniverse (rvs _) ∧ _ = Function.update y0 j (iRVMul s0 (y0 j))) ↔
    ((w ∘ blownIndex k) ∘ headIndex (1 + k) (1 + (1 + k)) ∈ sortedUniverse (fun _ => SortTag.rv) ∧
      updateMap j ((w ∘ blownIndex k) ∘ headIndex (1 + k) (1 + (1 + k))) =
        (w ∘ blownIndex k) ∘ tailIndex (1 + k) (1 + (1 + k))) ∧ w ∈ sortedUniverse _
  rw [e1, e2, updateMap_join]
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨⟨fun i => ?_, he.symm⟩, hs⟩
    rw [← e1]
    exact hs _
  · rintro ⟨⟨-, he⟩, hs⟩
    exact ⟨hs, he.symm⟩

end Blown

/-! ### The endpoint schema -/

namespace DatumSchema
variable {k : ℕ} (D : DatumSchema B sp k)

/-- Index map of `(z, u, y0)` in the layout `(z, u, y, y0, t)`. -/
def endIdxC (p a k : ℕ) : Fin ((p + a) + (1 + k)) → Fin (((p + a) + (1 + k)) + ((1 + k) + 1)) :=
  Fin.append (Fin.castAdd _ ∘ Fin.castAdd (1 + k)) (fun i => Fin.natAdd ((p + a) + (1 + k)) (Fin.castAdd 1 i))

/-- Index map of `(z, u, t)` in the layout `(z, u, y, y0, t)`. -/
def endIdxA (p a k : ℕ) : Fin ((p + a) + 1) → Fin (((p + a) + (1 + k)) + ((1 + k) + 1)) :=
  Fin.append (Fin.castAdd _ ∘ Fin.castAdd (1 + k)) (fun _ => Fin.natAdd ((p + a) + (1 + k)) (Fin.natAdd (1 + k) 0))

/-- Index map of `(y0, t, y)` in the layout `(z, u, y, y0, t)`. -/
def endIdxB (p a k : ℕ) : Fin (((1 + k) + 1) + (1 + k)) → Fin (((p + a) + (1 + k)) + ((1 + k) + 1)) :=
  Fin.append (fun i => Fin.natAdd ((p + a) + (1 + k)) i) (fun i => Fin.castAdd _ (Fin.natAdd (p + a) i))

/-- The structural-map relation of the endpoint, in the layout `(z, u, y)`. -/
def endCoord : Set (Fin ((p + D.chart.arity) + (1 + k)) → M) :=
  {w | ∃ v : Fin ((1 + k) + 1) → M, Fin.append w v ∈
    ({x | x ∘ endIdxC p D.chart.arity k ∈ D.chart.coord ∧ x ∈ sortedUniverse
        (Fin.append (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs (1 + k))) (rvs ((1 + k) + 1)))} ∩
      {x | x ∘ endIdxA p D.chart.arity k ∈ D.aperture ∧ x ∈ sortedUniverse
        (Fin.append (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs (1 + k))) (rvs ((1 + k) + 1)))}) ∩
      {x | x ∘ endIdxB p D.chart.arity k ∈ blownSet D.coordinate ∧ x ∈ sortedUniverse
        (Fin.append (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs (1 + k))) (rvs ((1 + k) + 1)))}}

theorem endCoord_definable :
    DefinableOverBase B (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs (1 + k))) D.endCoord :=
  gamma_family_row_exists_definable _ (rvs ((1 + k) + 1))
    (((D.chart.coord_definable.preimage_real _ _).inter (D.aperture_definable.preimage_real _ _)).inter
      ((blownSet_definable D.coordinate).preimage_real _ _))

/-- The endpoint schema of a datum schema: rows `u ↦ (u, τ(u))`, with `f`
having `τ(u) · f_j(u)` in position `j`. -/
def endSchema : ChartSchema B sp (1 + k) where
  arity := D.chart.arity
  domain := D.chart.domain
  domain_definable := D.chart.domain_definable
  coord := D.endCoord
  coord_definable := D.endCoord_definable
  volume := D.chart.volume
  volume_definable := D.chart.volume_definable
  bound := D.inactiveBound

section EndValues
variable {a : ℕ} (z : Fin p → M) (u : Fin a → M) (y y0 : Fin (1 + k) → M) (t : M)

omit hM in
theorem end_idxC : Fin.append (Fin.append (Fin.append z u) y) (Fin.append y0 (fun _ : Fin 1 => t)) ∘
    endIdxC p a k = Fin.append (Fin.append z u) y0 := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [endIdxC]
  · simp [endIdxC]

omit hM in
theorem end_idxA : Fin.append (Fin.append (Fin.append z u) y) (Fin.append y0 (fun _ : Fin 1 => t)) ∘
    endIdxA p a k = Fin.append (Fin.append z u) (fun _ : Fin 1 => t) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [endIdxA]
  · simp [endIdxA]

omit hM in
theorem end_idxB : Fin.append (Fin.append (Fin.append z u) y) (Fin.append y0 (fun _ : Fin 1 => t)) ∘
    endIdxB p a k = Fin.append (Fin.append y0 (fun _ : Fin 1 => t)) y := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [endIdxB]
  · simp [endIdxB]

end EndValues

omit hM in
theorem append_decomp_one {n : ℕ} (v : Fin (n + 1) → M) :
    v = Fin.append (fun i => v (Fin.castAdd 1 i)) (fun _ : Fin 1 => v (Fin.natAdd n 0)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp
  · fin_cases l; simp

omit hM in
theorem blown_sorted {y0 y : Fin (1 + k) → M} {t : M} (h0 : ∀ i, sortEval SortTag.rv (y0 i))
    (ht : sortEval SortTag.rv t) (hy : ∀ i, sortEval SortTag.rv (y i)) :
    Fin.append (Fin.append y0 (fun _ : Fin 1 => t)) y ∈ sortedUniverse (rvs (((1 + k) + 1) + (1 + k))) := by
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l
    · simpa using h0 r
    · simpa using ht
  · simpa using hy l

theorem mem_blownSet_iff (j : Fin (1 + k)) (y0 y : Fin (1 + k) → M) (t : M)
    (hs : Fin.append (Fin.append y0 (fun _ : Fin 1 => t)) y ∈ sortedUniverse (rvs _)) :
    Fin.append (Fin.append y0 (fun _ : Fin 1 => t)) y ∈ blownSet j ↔ y = Function.update y0 j (iRVMul t (y0 j)) := by
  simp only [blownSet, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]
  exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩

theorem mem_rows_sorted_param (sp : Fin p → SortTag) {a d : ℕ} (sx : Fin a → SortTag) (sy : Fin d → SortTag)
    {D : Set (Fin ((p + a) + d) → M)} (hD : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) D)
    {z : Fin p → M} {x : Fin a → M} {y : Fin d → M} (h : Fin.append (Fin.append z x) y ∈ D) :
    ∀ i, sortEval (sp i) (z i) := by
  intro i
  have := hD.proper _ h (Fin.castAdd d (Fin.castAdd a i))
  rwa [Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left] at this

theorem endSchema_coordRow (z : Fin p → M) (u : Fin D.chart.arity → M) (y : Fin (1 + k) → M) :
    D.endSchema.coordRow z u y ↔ ∃ y0 t, D.chart.coordRow z u y0 ∧ D.apRow z u t ∧
      y = Function.update y0 D.coordinate (iRVMul t (y0 D.coordinate)) := by
  change Fin.append (Fin.append z u) y ∈ D.endCoord ↔ _
  constructor
  · rintro ⟨v, ⟨⟨hC, -⟩, ⟨hA, -⟩⟩, ⟨hB, hs⟩⟩
    rw [append_decomp_one v] at hC hA hB hs
    rw [end_idxC] at hC
    rw [end_idxA] at hA
    rw [end_idxB] at hB
    refine ⟨_, _, hC, hA, ?_⟩
    exact (mem_blownSet_iff D.coordinate _ y _ hB.1).mp hB
  · rintro ⟨y0, t, hC, hA, rfl⟩
    have hzs := mem_rows_sorted_param sp (rvs D.chart.arity) (rvs (1 + k)) D.chart.coord_definable hC
    have hCs := mem_rows_sorted sp (rvs D.chart.arity) (rvs (1 + k)) D.chart.coord_definable hC
    have hAs := mem_rows_sorted sp (rvs D.chart.arity) (rvs 1) D.aperture_definable hA
    have ht : sortEval SortTag.rv t := hAs.2 0
    have hy : ∀ i, sortEval SortTag.rv (Function.update y0 D.coordinate (iRVMul t (y0 D.coordinate)) i) := by
      intro i
      by_cases hi : i = D.coordinate
      · subst hi
        rw [Function.update_self]
        exact rv_mul_mem hM ht (hCs.2 _)
      · rw [Function.update_of_ne hi]
        exact hCs.2 i
    have hv : ∀ j, sortEval SortTag.rv ((Fin.append y0 (fun _ : Fin 1 => t)) j) := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa using hCs.2 l
      · simpa using ht
    have hs : Fin.append (Fin.append (Fin.append z u) (Function.update y0 D.coordinate (iRVMul t (y0 D.coordinate))))
        (Fin.append y0 (fun _ : Fin 1 => t)) ∈ sortedUniverse
          (Fin.append (Fin.append (Fin.append sp (rvs D.chart.arity)) (rvs (1 + k))) (rvs ((1 + k) + 1))) :=
      sorted_append (sorted_append (sorted_append hzs hCs.1) hy) hv
    refine ⟨Fin.append y0 (fun _ => t), ⟨⟨?_, hs⟩, ⟨?_, hs⟩⟩, ⟨?_, hs⟩⟩
    · rw [end_idxC]; exact hC
    · rw [end_idxA]; exact hA
    · rw [end_idxB, mem_blownSet_iff _ _ _ _ (blown_sorted hCs.2 ht hy)]

variable {D}

theorem endSchema_coordRow_iff {z : Fin p → M} (hz : D.Valid z) (u : Fin D.chart.arity → M) (y : Fin (1 + k) → M) :
    D.endSchema.coordRow z u y ↔ u ∈ D.chart.row z ∧
      y = Function.update (D.chart.coordAt z u) D.coordinate (iRVMul (D.apAt z u) (D.chart.coordAt z u D.coordinate)) := by
  rw [endSchema_coordRow]
  constructor
  · rintro ⟨y0, t, hC, hA, rfl⟩
    obtain ⟨hu, rfl⟩ := (ChartSchema.coordRow_iff hz.chart u y0).mp hC
    obtain ⟨-, rfl⟩ := (apRow_iff hz u t).mp hA
    exact ⟨hu, rfl⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨_, _, ChartSchema.coordRow_coordAt hz.chart hu, apRow_apAt hz hu, rfl⟩

theorem inactRel_of_blown {z : Fin p → M} (hz : D.Valid z) {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.row z)
    {y : Fin (1 + k) → M} {s : M}
    (hy : y = Function.update (D.chart.coordAt z u) D.coordinate (iRVMul s (D.chart.coordAt z u D.coordinate))) :
    D.inactRel z u y := by
  refine ⟨D.chart.coordAt z u D.coordinate, ?_⟩
  have he : Function.update y D.coordinate (D.chart.coordAt z u D.coordinate) = D.chart.coordAt z u := by
    rw [hy, Function.update_idem, Function.update_eq_self]
  rw [he]
  exact ChartSchema.coordRow_coordAt hz.chart hu

/-- The endpoint schema is valid where the datum schema is. -/
theorem Valid.endSchema {z : Fin p → M} (hz : D.Valid z) : D.endSchema.Valid z := by
  have hc := hz.chart
  refine ⟨⟨hc.sorted, ?_, ?_, ?_⟩, ?_, hc.vol_total, hc.vol_dom, hc.vol_same, hc.bounded⟩
  · intro u hu
    refine ⟨_, (endSchema_coordRow_iff hz u _).mpr ⟨hu, rfl⟩, fun y hy => ?_⟩
    exact ((endSchema_coordRow_iff hz u y).mp hy).2
  · intro u y hy
    exact ((endSchema_coordRow_iff hz u y).mp hy).1
  · intro y hyrv
    have hsub : {x : Fin D.chart.arity → M | Fin.append (Fin.append z x) y ∈ D.endSchema.coord} ⊆
        {u | D.inactRel z u y} := by
      intro u hu
      obtain ⟨hu', hy⟩ := (endSchema_coordRow_iff hz u y).mp hu
      exact inactRel_of_blown hz hu' hy
    obtain ⟨hfin, hle⟩ := hz.inactive y hyrv
    exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans hle⟩
  · intro u y hy
    obtain ⟨hu, rfl⟩ := (endSchema_coordRow_iff hz u y).mp hy
    intro i
    by_cases hi : i = D.coordinate
    · subst hi
      rw [Function.update_self]
      exact nonzero_mul (hz.ap_value u _ (apRow_apAt hz hu)).1 (ChartSchema.coordAt_proper hc hu _)
    · rw [Function.update_of_ne hi]
      exact ChartSchema.coordAt_proper hc hu i

end DatumSchema

end DiamondIntegral.Section7.Lemma714Schema
