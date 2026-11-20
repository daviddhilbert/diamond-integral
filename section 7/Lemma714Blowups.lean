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

/-! ### The shell schema -/

section Shell
variable (D)

/-- `1 < codeValue s` on a single nonzero code. -/
def oneLtFormula : GammaOrderLogic.Formula Unit 1 := .ex (.and (.unary () 0) (.lt 0 1))

theorem oneLt_definable :
    DefinableOverBase B (fun _ : Fin 1 => .rv) {z : Fin 1 → M | Proper z ∧ 1 < codeValue (z 0)} := by
  have h := GammaOrderLogic.formula_definable_base B (fun _ : Unit => ({1} : Set (Values.Gamma (M := M))))
    (fun _ => GammaGroupNames.one_definable_base B) oneLtFormula
  unfold GammaOrderLogic.GammaDefinable at h
  convert h using 3 with z
  simp only [oneLtFormula, GammaOrderLogic.Formula.Realize, Fin.cons_zero, Fin.cons_one,
    Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]

section Index
variable (p a k : ℕ)
/-- `(z, u)` inside `(z, u, s, t)`. -/
def shIdxD : Fin (p + a) → Fin ((p + (a + 1)) + 1) :=
  Fin.append (fun i => Fin.castAdd 1 (Fin.castAdd (a + 1) i)) (fun i => Fin.castAdd 1 (Fin.natAdd p (Fin.castAdd 1 i)))
/-- `(z, u, t)` inside `(z, u, s, t)`. -/
def shIdxA : Fin ((p + a) + 1) → Fin ((p + (a + 1)) + 1) :=
  Fin.append (shIdxD p a) (fun _ => Fin.natAdd (p + (a + 1)) 0)
/-- `s` inside `(z, u, s, t)`. -/
def shIdxS : Fin ((p + (a + 1)) + 1) := Fin.castAdd 1 (Fin.natAdd p (Fin.natAdd a 0))
/-- `t` inside `(z, u, s, t)`. -/
def shIdxT : Fin ((p + (a + 1)) + 1) := Fin.natAdd (p + (a + 1)) 0
/-- `(z, u, y0)` inside `(z, u, s, y, y0)`. -/
def shIdxC : Fin ((p + a) + (1 + k)) → Fin (((p + (a + 1)) + (1 + k)) + (1 + k)) :=
  Fin.append (Fin.append (fun i => Fin.castAdd (1 + k) (Fin.castAdd (1 + k) (Fin.castAdd (a + 1) i)))
    (fun i => Fin.castAdd (1 + k) (Fin.castAdd (1 + k) (Fin.natAdd p (Fin.castAdd 1 i)))))
    (fun i => Fin.natAdd ((p + (a + 1)) + (1 + k)) i)
/-- `(y0, s, y)` inside `(z, u, s, y, y0)`. -/
def shIdxB : Fin (((1 + k) + 1) + (1 + k)) → Fin (((p + (a + 1)) + (1 + k)) + (1 + k)) :=
  Fin.append (Fin.append (fun i => Fin.natAdd ((p + (a + 1)) + (1 + k)) i)
    (fun _ => Fin.castAdd (1 + k) (Fin.castAdd (1 + k) (Fin.natAdd p (Fin.natAdd a 0)))))
    (fun i => Fin.castAdd (1 + k) (Fin.natAdd (p + (a + 1)) i))
/-- `(z, u, c)` inside `(z, u, s, c)`. -/
def shIdxV : Fin ((p + a) + 1) → Fin ((p + (a + 1)) + 1) :=
  Fin.append (shIdxD p a) (fun _ => Fin.natAdd (p + (a + 1)) 0)
end Index

/-- The shell domain in the layout `(z, u, s)`. -/
def shellDom : Set (Fin (p + (D.chart.arity + 1)) → M) :=
  let st := Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs 1)
  {v | ∃ tt : Fin 1 → M, Fin.append v tt ∈
    (({x | x ∘ shIdxD p D.chart.arity ∈ D.chart.domain ∧ x ∈ sortedUniverse st} ∩
      {x | x ∘ shIdxA p D.chart.arity ∈ D.aperture ∧ x ∈ sortedUniverse st}) ∩
      ({x | x ∘ ![shIdxS p D.chart.arity] ∈ {z : Fin 1 → M | Proper z ∧ 1 < codeValue (z 0)} ∧
          x ∈ sortedUniverse st} ∩
        {x | x ∘ ![shIdxT p D.chart.arity, shIdxS p D.chart.arity] ∈
          {z : Fin 2 → M | Proper z ∧ codeValue (z 1) ≤ codeValue (z 0)} ∧ x ∈ sortedUniverse st}))}

theorem shellDom_definable : DefinableOverBase B (Fin.append sp (rvs (D.chart.arity + 1))) D.shellDom :=
  gamma_family_row_exists_definable _ (rvs 1)
    (((D.chart.domain_definable.preimage_real _ _).inter (D.aperture_definable.preimage_real _ _)).inter
      ((oneLt_definable.preimage_real _ _).inter (DatumSchema.le_codes_definable.preimage_real _ _)))

/-- The shell structural-map relation in the layout `(z, u, s, y)`. -/
def shellCoord : Set (Fin ((p + (D.chart.arity + 1)) + (1 + k)) → M) :=
  let st := Fin.append (Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs (1 + k))) (rvs (1 + k))
  {w | ∃ y0 : Fin (1 + k) → M, Fin.append w y0 ∈
    ({x | x ∘ (Fin.castAdd (1 + k) ∘ Fin.castAdd (1 + k)) ∈ D.shellDom ∧ x ∈ sortedUniverse st} ∩
      {x | x ∘ shIdxC p D.chart.arity k ∈ D.chart.coord ∧ x ∈ sortedUniverse st}) ∩
      {x | x ∘ shIdxB p D.chart.arity k ∈ blownSet D.coordinate ∧ x ∈ sortedUniverse st}}

theorem shellCoord_definable :
    DefinableOverBase B (Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs (1 + k))) D.shellCoord :=
  gamma_family_row_exists_definable _ (rvs (1 + k))
    (((D.shellDom_definable.preimage_real _ _).inter (D.chart.coord_definable.preimage_real _ _)).inter
      ((blownSet_definable D.coordinate).preimage_real _ _))

/-- The shell volume relation in the layout `(z, u, s, c)`. -/
def shellVol : Set (Fin ((p + (D.chart.arity + 1)) + 1) → M) :=
  let st := Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs 1)
  {x | x ∘ Fin.castAdd 1 ∈ D.shellDom ∧ x ∈ sortedUniverse st} ∩
    {x | x ∘ shIdxV p D.chart.arity ∈ D.chart.volume ∧ x ∈ sortedUniverse st}

theorem shellVol_definable :
    DefinableOverBase B (Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs 1)) D.shellVol :=
  (D.shellDom_definable.preimage_real _ _).inter (D.chart.volume_definable.preimage_real _ _)

/-- The shell schema of a datum schema: rows `(u, s)` with `1 < vrv s ≤ vrv τ(u)`,
structural map `f` with `s · f_j(u)` in position `j`, volume of `U`. -/
def shellSchema : ChartSchema B sp (1 + k) where
  arity := D.chart.arity + 1
  domain := D.shellDom
  domain_definable := D.shellDom_definable
  coord := D.shellCoord
  coord_definable := D.shellCoord_definable
  volume := D.shellVol
  volume_definable := D.shellVol_definable
  bound := D.inactiveBound

section ShellValues
variable {a : ℕ} (z : Fin p → M) (u : Fin a → M) (s0 t c : M) (y y0 : Fin (1 + k) → M)

omit hM in
theorem sh_idxD : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => t) ∘ shIdxD p a =
    Fin.append z u := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp [shIdxD]

omit hM in
theorem sh_idxA : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => t) ∘ shIdxA p a =
    Fin.append (Fin.append z u) (fun _ : Fin 1 => t) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [shIdxA, shIdxD]
  · simp [shIdxA]

omit hM in
theorem sh_idxST : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => t) ∘
    ![shIdxT p a, shIdxS p a] = ![t, s0] := by
  funext i
  fin_cases i <;> simp [shIdxS, shIdxT]

omit hM in
theorem sh_idxS : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => t) ∘
    ![shIdxS p a] = ![s0] := by
  funext i
  fin_cases i
  simp [shIdxS]

omit hM in
theorem sh_idxDom : Fin.append (Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) y) y0 ∘
    (Fin.castAdd (1 + k) ∘ Fin.castAdd (1 + k)) = Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) := by
  funext i
  simp

omit hM in
theorem sh_idxC : Fin.append (Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) y) y0 ∘
    shIdxC p a k = Fin.append (Fin.append z u) y0 := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [shIdxC]
  · simp [shIdxC]

omit hM in
theorem sh_idxB : Fin.append (Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) y) y0 ∘
    shIdxB p a k = Fin.append (Fin.append y0 (fun _ : Fin 1 => s0)) y := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [shIdxB]
  · simp [shIdxB]

omit hM in
theorem sh_idxV : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => c) ∘
    shIdxV p a = Fin.append (Fin.append z u) (fun _ : Fin 1 => c) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;> simp [shIdxV, shIdxD]
  · simp [shIdxV]

end ShellValues

omit hM in
theorem fin_one_eta (tt : Fin 1 → M) : tt = fun _ => tt 0 := by
  funext i; fin_cases i; rfl

theorem codeValue_of_not_nonzero {a : M} (h : ¬ NonzeroRV a) : codeValue a = 1 := by
  unfold codeValue
  rw [dif_neg h]

theorem nonzero_of_one_lt_le {s0 t : M} (h1 : 1 < codeValue s0) (hle : codeValue s0 ≤ codeValue t) :
    NonzeroRV t := by
  by_contra h
  rw [codeValue_of_not_nonzero h] at hle
  exact absurd (lt_of_lt_of_le h1 hle) (lt_irrefl 1)

theorem mem_shellDom (z : Fin p → M) (u : Fin D.chart.arity → M) (s0 : M) :
    Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) ∈ D.shellDom ↔
      Fin.append z u ∈ D.chart.domain ∧ NonzeroRV s0 ∧ 1 < codeValue s0 ∧
        ∃ t, D.apRow z u t ∧ codeValue s0 ≤ codeValue t := by
  constructor
  · rintro ⟨tt, ⟨⟨hD, -⟩, ⟨hA, -⟩⟩, ⟨⟨hS, -⟩, ⟨hT, -⟩⟩⟩
    rw [fin_one_eta tt] at hD hA hS hT
    rw [sh_idxD] at hD
    rw [sh_idxA] at hA
    rw [sh_idxS] at hS
    rw [sh_idxST] at hT
    refine ⟨hD, hS.1 0, by simpa using hS.2, _, hA, by simpa using hT.2⟩
  · rintro ⟨hD, hs, h1, t, hA, hle⟩
    have hzs := mem_rows_sorted_param sp (rvs D.chart.arity) (rvs 1) D.aperture_definable hA
    have hAs := mem_rows_sorted sp (rvs D.chart.arity) (rvs 1) D.aperture_definable hA
    have ht : sortEval SortTag.rv t := hAs.2 0
    have hus : ∀ j, sortEval SortTag.rv ((Fin.append u (fun _ : Fin 1 => s0)) j) := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · rw [Fin.append_left]; exact hAs.1 l
      · rw [Fin.append_right]; exact hs.1
    have hst : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => t) ∈
        sortedUniverse (Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs 1)) :=
      sorted_append (sorted_append hzs hus) (fun _ => ht)
    have htn : NonzeroRV t := nonzero_of_one_lt_le h1 hle
    refine ⟨fun _ => t, ⟨⟨?_, hst⟩, ⟨?_, hst⟩⟩, ⟨⟨?_, hst⟩, ⟨?_, hst⟩⟩⟩
    · rw [sh_idxD]; exact hD
    · rw [sh_idxA]; exact hA
    · rw [sh_idxS]; exact ⟨fun l => by fin_cases l; exact hs, by simpa using h1⟩
    · rw [sh_idxST]
      refine ⟨fun l => ?_, by simpa using hle⟩
      fin_cases l
      · exact htn
      · exact hs

theorem shell_coordRow (z : Fin p → M) (u : Fin D.chart.arity → M) (s0 : M) (y : Fin (1 + k) → M) :
    D.shellSchema.coordRow z (Fin.append u (fun _ : Fin 1 => s0)) y ↔
      Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) ∈ D.shellDom ∧
        ∃ y0, D.chart.coordRow z u y0 ∧ y = Function.update y0 D.coordinate (iRVMul s0 (y0 D.coordinate)) := by
  change Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) y ∈ D.shellCoord ↔ _
  constructor
  · rintro ⟨y0, ⟨⟨hD, -⟩, ⟨hC, -⟩⟩, ⟨hB, -⟩⟩
    rw [sh_idxDom] at hD
    rw [sh_idxC] at hC
    rw [sh_idxB] at hB
    exact ⟨hD, y0, hC, (mem_blownSet_iff D.coordinate y0 y s0 hB.1).mp hB⟩
  · rintro ⟨hD, y0, hC, rfl⟩
    have hDs := D.shellDom_definable.proper _ hD
    have hCs := mem_rows_sorted sp (rvs D.chart.arity) (rvs (1 + k)) D.chart.coord_definable hC
    have hs0 : sortEval SortTag.rv s0 := by
      have := hDs (Fin.natAdd p (Fin.natAdd D.chart.arity 0))
      simpa using this
    have hy : ∀ i, sortEval SortTag.rv (Function.update y0 D.coordinate (iRVMul s0 (y0 D.coordinate)) i) := by
      intro i
      by_cases hi : i = D.coordinate
      · subst hi
        rw [Function.update_self]
        exact rv_mul_mem hM hs0 (hCs.2 _)
      · rw [Function.update_of_ne hi]
        exact hCs.2 i
    have hst : Fin.append (Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0)))
        (Function.update y0 D.coordinate (iRVMul s0 (y0 D.coordinate)))) y0 ∈ sortedUniverse
          (Fin.append (Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs (1 + k))) (rvs (1 + k))) :=
      sorted_append (sorted_append hDs hy) hCs.2
    refine ⟨y0, ⟨⟨?_, hst⟩, ⟨?_, hst⟩⟩, ⟨?_, hst⟩⟩
    · rw [sh_idxDom]; exact hD
    · rw [sh_idxC]; exact hC
    · rw [sh_idxB, mem_blownSet_iff _ _ _ _ (blown_sorted hCs.2 hs0 hy)]

theorem shell_volRow (z : Fin p → M) (u : Fin D.chart.arity → M) (s0 c : M) :
    D.shellSchema.volRow z (Fin.append u (fun _ : Fin 1 => s0)) c ↔
      Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) ∈ D.shellDom ∧ D.chart.volRow z u c := by
  change Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => c) ∈ D.shellVol ↔ _
  constructor
  · rintro ⟨⟨hD, -⟩, ⟨hV, -⟩⟩
    rw [ChartSchema.append_comp_castAdd] at hD
    rw [sh_idxV] at hV
    exact ⟨hD, hV⟩
  · rintro ⟨hD, hV⟩
    have hDs := D.shellDom_definable.proper _ hD
    have hVs := mem_rows_sorted sp (rvs D.chart.arity) (rvs 1) D.chart.volume_definable hV
    have hst : Fin.append (Fin.append z (Fin.append u (fun _ : Fin 1 => s0))) (fun _ : Fin 1 => c) ∈
        sortedUniverse (Fin.append (Fin.append sp (rvs (D.chart.arity + 1))) (rvs 1)) :=
      sorted_append hDs hVs.2
    refine ⟨⟨?_, hst⟩, ⟨?_, hst⟩⟩
    · rw [ChartSchema.append_comp_castAdd]; exact hD
    · rw [sh_idxV]; exact hV

theorem shell_decomp (us : Fin (D.chart.arity + 1) → M) :
    us = Fin.append (fun i => us (Fin.castAdd 1 i)) (fun _ : Fin 1 => us (Fin.natAdd D.chart.arity 0)) :=
  append_decomp_one us

variable {D}

theorem shell_coordRow_iff {z : Fin p → M} (hz : D.Valid z) (u : Fin D.chart.arity → M) (s0 : M)
    (y : Fin (1 + k) → M) :
    D.shellSchema.coordRow z (Fin.append u (fun _ : Fin 1 => s0)) y ↔
      Fin.append z (Fin.append u (fun _ : Fin 1 => s0)) ∈ D.shellDom ∧
        y = Function.update (D.chart.coordAt z u) D.coordinate (iRVMul s0 (D.chart.coordAt z u D.coordinate)) := by
  rw [shell_coordRow]
  constructor
  · rintro ⟨hD, y0, hC, rfl⟩
    obtain ⟨-, rfl⟩ := (ChartSchema.coordRow_iff hz.chart u y0).mp hC
    exact ⟨hD, rfl⟩
  · rintro ⟨hD, rfl⟩
    have hu := ((D.mem_shellDom z u s0).mp hD).1
    exact ⟨hD, _, ChartSchema.coordRow_coordAt hz.chart hu, rfl⟩

/-- The shell schema is valid where the datum schema is. -/
theorem Valid.shellSchema {z : Fin p → M} (hz : D.Valid z) : D.shellSchema.Valid z := by
  have hc := hz.chart
  refine ⟨⟨hc.sorted, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro us hus
    rw [append_decomp_one (n := D.chart.arity) us] at hus ⊢
    refine ⟨_, (shell_coordRow_iff hz _ _ _).mpr ⟨hus, rfl⟩, fun y hy => ?_⟩
    exact ((shell_coordRow_iff hz _ _ y).mp hy).2
  · intro us y hy
    have hy' : D.shellSchema.coordRow z us y := hy
    rw [append_decomp_one (n := D.chart.arity) us] at hy' ⊢
    exact ((shell_coordRow_iff hz _ _ y).mp hy').1
  · intro y hyrv
    let S := {us : Fin (D.chart.arity + 1) → M | Fin.append (Fin.append z us) y ∈ D.shellSchema.coord}
    let f : (Fin (D.chart.arity + 1) → M) → (Fin D.chart.arity → M) := fun us i => us (Fin.castAdd 1 i)
    have hmaps : Set.MapsTo f S {u | D.inactRel z u y} := by
      intro us hus
      have hus' : D.shellSchema.coordRow z us y := hus
      rw [append_decomp_one (n := D.chart.arity) us] at hus'
      obtain ⟨hD, hy⟩ := (shell_coordRow_iff hz _ _ y).mp hus'
      exact inactRel_of_blown hz ((D.mem_shellDom z _ _).mp hD).1 hy
    have hinj : Set.InjOn f S := by
      intro us hus us' hus' he
      have h1 : D.shellSchema.coordRow z us y := hus
      have h2 : D.shellSchema.coordRow z us' y := hus'
      rw [append_decomp_one (n := D.chart.arity) us] at h1
      rw [append_decomp_one (n := D.chart.arity) us'] at h2
      obtain ⟨hD1, hy1⟩ := (shell_coordRow_iff hz _ _ y).mp h1
      obtain ⟨hD2, hy2⟩ := (shell_coordRow_iff hz _ _ y).mp h2
      have hu : (fun i => us (Fin.castAdd 1 i)) = fun i => us' (Fin.castAdd 1 i) := he
      rw [hu] at hy1 hD1
      have hd1 := (D.mem_shellDom z _ _).mp hD1
      have hd2 := (D.mem_shellDom z _ _).mp hD2
      have hj := congrFun (hy1.symm.trans hy2) D.coordinate
      simp only [Function.update_self] at hj
      have hs := rvMul_right_cancel hd1.2.1.1 hd2.2.1.1 (ChartSchema.coordAt_proper hc hd2.1 _) hj
      rw [append_decomp_one (n := D.chart.arity) us, append_decomp_one (n := D.chart.arity) us', hu, hs]
    obtain ⟨hfin, hle⟩ := hz.inactive y hyrv
    exact ⟨Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.mpr hmaps)) hinj,
      (Set.ncard_le_ncard_of_injOn f hmaps hinj hfin).trans hle⟩
  · intro us y hy
    rw [append_decomp_one (n := D.chart.arity) us] at hy
    obtain ⟨hD, rfl⟩ := (shell_coordRow_iff hz _ _ y).mp hy
    have hd := (D.mem_shellDom z _ _).mp hD
    intro i
    by_cases hi : i = D.coordinate
    · subst hi
      rw [Function.update_self]
      exact nonzero_mul hd.2.1 (ChartSchema.coordAt_proper hc hd.1 _)
    · rw [Function.update_of_ne hi]
      exact ChartSchema.coordAt_proper hc hd.1 i
  · intro us hus
    have hus' : Fin.append z us ∈ D.shellDom := hus
    rw [append_decomp_one (n := D.chart.arity) us] at hus' ⊢
    obtain ⟨c, hcv⟩ := hc.vol_total _ ((D.mem_shellDom z _ _).mp hus').1
    exact ⟨c, (D.shell_volRow z _ _ c).mpr ⟨hus', hcv⟩⟩
  · intro us c h
    rw [append_decomp_one (n := D.chart.arity) us] at h ⊢
    obtain ⟨hD, hV⟩ := (D.shell_volRow z _ _ c).mp h
    exact ⟨hD, (hc.vol_dom _ c hV).2⟩
  · intro us c c' h h0 h0'
    rw [append_decomp_one (n := D.chart.arity) us] at h ⊢
    obtain ⟨hD, hV⟩ := (D.shell_volRow z _ _ c).mp h
    rw [D.shell_volRow]
    constructor
    · rintro ⟨-, hV'⟩
      exact (hc.vol_same _ c c' hV h0 h0').mp hV'
    · intro he
      exact ⟨hD, (hc.vol_same _ c c' hV h0 h0').mpr he⟩
  · obtain ⟨lo, hi, hb⟩ := hc.bounded
    obtain ⟨Δ, hΔ⟩ := hz.ap_bounded
    refine ⟨min lo 1, max hi Δ, fun us hus i => ?_⟩
    have hus' : Fin.append z us ∈ D.shellDom := hus
    rw [append_decomp_one (n := D.chart.arity) us] at hus'
    obtain ⟨hu, -, h1, t, ht, hle⟩ := (D.mem_shellDom z _ _).mp hus'
    refine Fin.addCases (fun l hi0 => ?_) (fun l hi0 => ?_) i
    · obtain ⟨h₁, h₂⟩ := hb _ hu l hi0
      exact ⟨(min_le_left lo 1).trans h₁, h₂.trans (le_max_left hi Δ)⟩
    · fin_cases l
      have e : us (Fin.natAdd D.chart.arity 0) = us (Fin.natAdd D.chart.arity ((fun i => i) ⟨0, by omega⟩)) := rfl
      constructor
      · exact (min_le_right lo 1).trans (le_of_lt h1)
      · exact (hle.trans (hΔ _ _ ht)).trans (le_max_right hi Δ)

end Shell

end DatumSchema

end DiamondIntegral.Section7.Lemma714Schema
