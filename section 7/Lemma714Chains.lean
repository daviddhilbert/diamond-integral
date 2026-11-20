import «section 7».Lemma714Blowups

/-! Lemma 7.14, part 5: move, chain and witness schemata.

A move schema on a chart schema `X` is the uniform version of one explicit
single-datum blowup (`Lemma714Witness.Move`):

* a rest `R`, a datum schema `D` and a result `X'`;
* a piece `P` of `X` with isomorphism schemata `X|P ≅ R` and `X|Pᶜ ≅ D.chart`
  (so `[X] = [R] + [D.source]`);
* pieces `Q₁`, `Q₂` of `X'` with isomorphism schemata `X'|Q₁ ≅ R`,
  `X'|Q₂∖Q₁ ≅ shell(D)` and `X'|(Q₁∪Q₂)ᶜ ≅ endpoint(D)`
  (so `[X'] = [R] + [D.annularObject]`).

The coproducts of Section 4 never appear; the class equalities come from
definable two-piece partitions. A chain schema is a finite sequence of move
schemata, each starting at the result of the previous one. A witness schema
for `([X₀], [Y₀]) ∈ μIsp^db` consists of chains from `X₀` and `Y₀` and an
isomorphism schema between their ends; in degree `0` it is an isomorphism
schema `X₀ ≅ Y₀`. All validity loci are `B`-definable. -/

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
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

/-- The complement of a piece inside the sorted universe. -/
abbrev compl {n : ℕ} (sn : Fin n → SortTag) (P : Set (Fin n → M)) : Set (Fin n → M) := sortedUniverse sn \ P

/-! ### Move schemata -/

/-- One uniform single-datum blowup of `X`. -/
structure MoveSchema {k : ℕ} (X : ChartSchema B sp (1 + k)) where
  rest : ChartSchema B sp (1 + k)
  datum : DatumSchema B sp k
  result : ChartSchema B sp (1 + k)
  piece : Set (Fin (p + X.arity) → M)
  piece_definable : DefinableOverBase B (Fin.append sp (rvs X.arity)) piece
  q₁ : Set (Fin (p + result.arity) → M)
  q₁_definable : DefinableOverBase B (Fin.append sp (rvs result.arity)) q₁
  q₂ : Set (Fin (p + result.arity) → M)
  q₂_definable : DefinableOverBase B (Fin.append sp (rvs result.arity)) q₂
  isoRest : IsoSchema (X.restrict piece piece_definable) rest
  isoSrc : IsoSchema (X.restrict (compl _ piece) piece_definable.compl) datum.chart
  isoRest' : IsoSchema (result.restrict q₁ q₁_definable) rest
  isoShell : IsoSchema (result.restrict (q₂ \ q₁) (q₂_definable.sdiff q₁_definable)) datum.shellSchema
  isoEnd : IsoSchema (result.restrict (compl _ (q₁ ∪ q₂)) (q₁_definable.union q₂_definable).compl)
    datum.endSchema

namespace MoveSchema
variable {k : ℕ} {X : ChartSchema B sp (1 + k)} (μ : MoveSchema X)

/-- The move schema is valid at `z`. -/
structure Valid (z : Fin p → M) : Prop where
  rest : μ.rest.Valid z
  datum : μ.datum.Valid z
  result : μ.result.Valid z
  isoRest : μ.isoRest.Valid z
  isoSrc : μ.isoSrc.Valid z
  isoRest' : μ.isoRest'.Valid z
  isoShell : μ.isoShell.Valid z
  isoEnd : μ.isoEnd.Valid z

theorem valid_definable : DefinableOverBase B sp {z | μ.Valid z} := by
  have h := μ.rest.valid_definable.inter (μ.datum.valid_definable.inter (μ.result.valid_definable.inter
    (μ.isoRest.valid_definable.inter (μ.isoSrc.valid_definable.inter (μ.isoRest'.valid_definable.inter
      (μ.isoShell.valid_definable.inter μ.isoEnd.valid_definable))))))
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩⟩

end MoveSchema

/-! ### Chain schemata -/

/-- A chain of `m` move schemata starting at `X`. -/
inductive ChainSchema {k : ℕ} : ChartSchema B sp (1 + k) → ℕ → Type
  | nil (X : ChartSchema B sp (1 + k)) : ChainSchema X 0
  | cons {X : ChartSchema B sp (1 + k)} {m : ℕ} (μ : MoveSchema X) (tail : ChainSchema μ.result m) :
      ChainSchema X (m + 1)

namespace ChainSchema
variable {k : ℕ}

/-- The end of a chain. -/
def last : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → ChainSchema X m → ChartSchema B sp (1 + k)
  | X, _, nil _ => X
  | _, _, cons _ tail => tail.last

/-- Every move of the chain is valid at `z`. -/
def Valid : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → ChainSchema X m → (Fin p → M) → Prop
  | _, _, nil _, _ => True
  | _, _, cons μ tail, z => μ.Valid z ∧ tail.Valid z

theorem valid_definable : {X : ChartSchema B sp (1 + k)} → {m : ℕ} → (c : ChainSchema X m) →
    DefinableOverBase B sp {z | (∀ i, sortEval (sp i) (z i)) ∧ c.Valid z}
  | _, _, nil _ => by
    convert real_definableOverBase B sp _ (sortedUniverse_definable B.real sp) using 1
    ext z
    simp [Valid, sortedUniverse]
  | _, _, cons μ tail => by
    convert μ.valid_definable.inter (valid_definable tail) using 1
    ext z
    simp only [Valid, Set.mem_setOf_eq, Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

theorem Valid.last {X : ChartSchema B sp (1 + k)} {z : Fin p → M} (hX : X.Valid z) :
    {m : ℕ} → (c : ChainSchema X m) → c.Valid z → c.last.Valid z := by
  intro m c
  induction c with
  | nil X => intro _; exact hX
  | cons μ tail ih => intro h; exact ih h.1.result h.2

end ChainSchema

/-! ### Witness schemata -/

/-- A uniform witness for `([X₀], [Y₀]) ∈ μIsp^db` in degree `1 + k`. -/
structure WitnessSchema {k : ℕ} (X₀ Y₀ : ChartSchema B sp (1 + k)) where
  leftLength : ℕ
  rightLength : ℕ
  left : ChainSchema X₀ leftLength
  right : ChainSchema Y₀ rightLength
  final : IsoSchema left.last right.last

namespace WitnessSchema
variable {k : ℕ} {X₀ Y₀ : ChartSchema B sp (1 + k)} (W : WitnessSchema X₀ Y₀)

/-- The witness schema is valid at `z`. -/
structure Valid (z : Fin p → M) : Prop where
  source : X₀.Valid z
  target : Y₀.Valid z
  left : W.left.Valid z
  right : W.right.Valid z
  final : W.final.Valid z

theorem valid_definable : DefinableOverBase B sp {z | W.Valid z} := by
  have h := X₀.valid_definable.inter (Y₀.valid_definable.inter ((W.left.valid_definable).inter
    ((W.right.valid_definable).inter W.final.valid_definable)))
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1, h.2, ⟨h.1.sorted, h.3⟩, ⟨h.1.sorted, h.4⟩, h.5⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1.2, h.2.2.2.1.2, h.2.2.2.2⟩⟩

end WitnessSchema

/-- A uniform witness in degree `0`: an isomorphism schema. -/
structure WitnessSchema0 (X₀ Y₀ : ChartSchema B sp 0) where
  iso : IsoSchema X₀ Y₀

namespace WitnessSchema0
variable {X₀ Y₀ : ChartSchema B sp 0} (W : WitnessSchema0 X₀ Y₀)

/-- The degree-0 witness schema is valid at `z`. -/
structure Valid (z : Fin p → M) : Prop where
  source : X₀.Valid z
  target : Y₀.Valid z
  iso : W.iso.Valid z

theorem valid_definable : DefinableOverBase B sp {z | W.Valid z} := by
  convert X₀.valid_definable.inter (Y₀.valid_definable.inter W.iso.valid_definable) using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end WitnessSchema0

end DiamondIntegral.Section7.Lemma714Schema
