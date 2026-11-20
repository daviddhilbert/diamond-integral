import «section 7».FiberwiseInput

/-! Lemma 7.14, part 1: explicit witnesses for `μIsp^db`.

`MuIsp` is defined on classes: `x` and `y` have blowup chains with a common
class, a blowup of length one replacing finitely many summands at once
(`ElementaryBlowups.Step`). For the uniformisation in Lemma 7.14 a witness is
needed as explicit data, so that it can be coded by definable families.

* `Step1`: a blowup with one datum. Every `Step` with `N` data is a chain of
  `N` steps `Step1` (`steps1_of_step`), so `MuIsp = Common Step1`
  (`muIsp_iff_common_step1`).
* `Move X`: one explicit single-datum blowup of an object `X`: an object `rest`,
  an aperture datum `D` and an isomorphism `X ≅ rest ⊎ D.source`; its result is
  the object `rest ⊎ D.annularObject`. `Moves m X Y` is an explicit chain of
  `m` moves from `X` to `Y`.
* `muIsp_iff_moves`: `([X], [Y]) ∈ μIsp^db` iff there are explicit move chains
  `X ⇝ X'`, `Y ⇝ Y'` and an isomorphism `X' ≅ Y'`.
* `ispRel_iff_witness`: the same for `IspRel` in degree `1 + k`, and
  `ispRel_zero_iff` in degree `0` (an isomorphism, no moves).

No definability is involved; this is algebra in the class monoid. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Lemma714Witness
open DiamondIntegral.Section4
open RVMeasuredCharts RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.FiberwiseInput
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### Single-datum blowups on classes -/

/-- A blowup of length one with a single datum: one summand `[D.source]` of `x`
is replaced by `[D.annularObject]`. -/
def Step1 (x y : Cls B (1 + k)) : Prop :=
  ∃ (D : AnnularDatum B k) (z : Cls B (1 + k)), x = z + cls D.source ∧ y = z + cls D.annularObject

theorem step_of_step1 {x y : Cls B (1 + k)} (h : Step1 x y) : Step x y := by
  obtain ⟨D, z, hx, hy⟩ := h
  exact ⟨1, fun _ => D, z, by simpa using hx, by simpa using hy⟩

theorem steps_of_steps1 {n : ℕ} {x y : Cls B (1 + k)} (h : Steps (Step1 (B := B) (k := k)) n x y) :
    BlowupSteps n x y := by
  induction h with
  | refl a => exact .refl a
  | cons h _ ih => exact .cons (step_of_step1 h) ih

/-- A blowup of length one with `N` data is a chain of `N` single-datum
blowups. -/
theorem steps1_of_data : ∀ (N : ℕ) (D : Fin N → AnnularDatum B k) (z : Cls B (1 + k)),
    Steps (Step1 (B := B) (k := k)) N (z + ∑ i, cls (D i).source) (z + ∑ i, cls (D i).annularObject)
  | 0, _, z => by simpa using Steps.refl (R := Step1 (B := B) (k := k)) z
  | N + 1, D, z => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h1 : Step1 (z + (cls (D 0).source + ∑ i : Fin N, cls (D i.succ).source))
        (z + (cls (D 0).annularObject + ∑ i : Fin N, cls (D i.succ).source)) :=
      ⟨D 0, z + ∑ i : Fin N, cls (D i.succ).source, by abel, by abel⟩
    have h2 := steps1_of_data N (fun i => D i.succ) (z + cls (D 0).annularObject)
    refine .cons h1 ?_
    convert h2 using 1 <;> abel

theorem exists_steps1_of_step {x y : Cls B (1 + k)} (h : Step x y) :
    ∃ N, Steps (Step1 (B := B) (k := k)) N x y := by
  obtain ⟨N, D, z, rfl, rfl⟩ := h
  exact ⟨N, steps1_of_data N D z⟩

theorem exists_steps1_of_steps {n : ℕ} {x y : Cls B (1 + k)} (h : BlowupSteps n x y) :
    ∃ N, Steps (Step1 (B := B) (k := k)) N x y := by
  induction h with
  | refl a => exact ⟨0, .refl a⟩
  | cons h _ ih =>
    obtain ⟨N₁, h₁⟩ := exists_steps1_of_step h
    obtain ⟨N₂, h₂⟩ := ih
    exact ⟨N₁ + N₂, h₁.trans h₂⟩

/-- `μIsp^db` is the common-reduct relation of single-datum blowups. -/
theorem muIsp_iff_common_step1 (x y : Cls B (1 + k)) :
    MuIsp x y ↔ Common (Step1 (B := B) (k := k)) x y := by
  constructor
  · rintro ⟨c, m, n, hx, hy⟩
    obtain ⟨m', hx'⟩ := exists_steps1_of_steps hx
    obtain ⟨n', hy'⟩ := exists_steps1_of_steps hy
    exact ⟨c, m', n', hx', hy'⟩
  · rintro ⟨c, m, n, hx, hy⟩
    exact ⟨c, m, n, steps_of_steps1 hx, steps_of_steps1 hy⟩

/-! ### Explicit moves on objects -/

/-- One explicit single-datum blowup of `X`: `X ≅ rest ⊎ D.source`. -/
structure Move (X : Obj B (1 + k)) where
  rest : Obj B (1 + k)
  datum : AnnularDatum B k
  iso : Iso X.toChart (coprod rest datum.source).toChart

/-- The result `rest ⊎ D.annularObject` of a move. -/
def Move.result {X : Obj B (1 + k)} (μ : Move X) : Obj B (1 + k) :=
  coprod μ.rest μ.datum.annularObject

/-- Explicit chains of `m` moves from `X` to `Y`. -/
inductive Moves : ℕ → Obj B (1 + k) → Obj B (1 + k) → Type
  | refl (X : Obj B (1 + k)) : Moves 0 X X
  | cons {m : ℕ} {X Y : Obj B (1 + k)} (μ : Move X) (tail : Moves m μ.result Y) : Moves (m + 1) X Y

theorem Move.step1 {X : Obj B (1 + k)} (μ : Move X) : Step1 (cls X) (cls μ.result) :=
  ⟨μ.datum, cls μ.rest, (cls_eq_of_iso μ.iso).trans (cls_coprod _ _), cls_coprod _ _⟩

theorem Moves.steps1 {m : ℕ} {X Y : Obj B (1 + k)} (w : Moves m X Y) :
    Steps (Step1 (B := B) (k := k)) m (cls X) (cls Y) := by
  induction w with
  | refl X => exact .refl _
  | cons μ _ ih => exact .cons μ.step1 ih

/-- A single-datum blowup of the class of `X` is realized by an explicit move. -/
theorem exists_move_of_step1 {X : Obj B (1 + k)} {y : Cls B (1 + k)} (h : Step1 (cls X) y) :
    ∃ μ : Move X, cls μ.result = y := by
  obtain ⟨D, z, hx, rfl⟩ := h
  obtain ⟨R, rfl⟩ := cls_surjective z
  have he : cls X = cls (coprod R D.source) := hx.trans (cls_coprod R D.source).symm
  obtain ⟨F⟩ := cls_eq_iff.mp he
  exact ⟨⟨R, D, F⟩, cls_coprod _ _⟩

theorem exists_moves_of_steps1 {m : ℕ} {x y : Cls B (1 + k)} (h : Steps (Step1 (B := B) (k := k)) m x y) :
    ∀ X : Obj B (1 + k), cls X = x → ∃ Y : Obj B (1 + k), cls Y = y ∧ Nonempty (Moves m X Y) := by
  induction h with
  | refl a =>
    intro X hX
    exact ⟨X, hX, ⟨.refl X⟩⟩
  | cons h _ ih =>
    intro X hX
    subst hX
    obtain ⟨μ, hμ⟩ := exists_move_of_step1 h
    obtain ⟨Y, hY, ⟨w⟩⟩ := ih μ.result hμ
    exact ⟨Y, hY, ⟨.cons μ w⟩⟩

/-- **Explicit witnesses for `μIsp^db`.** `([X], [Y]) ∈ μIsp^db` iff there are
explicit move chains `X ⇝ X'`, `Y ⇝ Y'` and an isomorphism `X' ≅ Y'`. -/
theorem muIsp_iff_moves (X Y : Obj B (1 + k)) :
    MuIsp (cls X) (cls Y) ↔ ∃ (m n : ℕ) (X' Y' : Obj B (1 + k)),
      Nonempty (Moves m X X') ∧ Nonempty (Moves n Y Y') ∧ Nonempty (Iso X'.toChart Y'.toChart) := by
  rw [muIsp_iff_common_step1]
  constructor
  · rintro ⟨c, m, n, hx, hy⟩
    obtain ⟨X', hX', wX⟩ := exists_moves_of_steps1 hx X rfl
    obtain ⟨Y', hY', wY⟩ := exists_moves_of_steps1 hy Y rfl
    exact ⟨m, n, X', Y', wX, wY, cls_eq_iff.mp (hX'.trans hY'.symm)⟩
  · rintro ⟨m, n, X', Y', ⟨wX⟩, ⟨wY⟩, ⟨F⟩⟩
    refine ⟨cls Y', m, n, ?_, wY.steps1⟩
    rw [← cls_eq_of_iso F]
    exact wX.steps1

/-! ### The same for `IspRel` -/

theorem castCls_rfl {m : ℕ} (x : Cls B m) : castCls rfl x = x := rfl

/-- `IspRel` in degree `1 + k` by explicit witnesses. -/
theorem ispRel_iff_witness (X Y : Obj B (1 + k)) :
    IspRel (cls X) (cls Y) ↔ ∃ (m n : ℕ) (X' Y' : Obj B (1 + k)),
      Nonempty (Moves m X X') ∧ Nonempty (Moves n Y Y') ∧ Nonempty (Iso X'.toChart Y'.toChart) := by
  rw [ispRel_iff rfl, castCls_rfl, castCls_rfl]
  exact muIsp_iff_moves X Y

/-- `IspRel` in degree `0` is an isomorphism. -/
theorem ispRel_zero_iff (X Y : Obj B 0) :
    IspRel (cls X) (cls Y) ↔ Nonempty (Iso X.toChart Y.toChart) := by
  rw [ispRel_zero]
  exact cls_eq_iff

/-- From explicit witnesses to `IspRel` in degree `1 + k`. -/
theorem ispRel_of_moves {X Y X' Y' : Obj B (1 + k)} {m n : ℕ} (wX : Moves m X X') (wY : Moves n Y Y')
    (F : Iso X'.toChart Y'.toChart) : IspRel (cls X) (cls Y) :=
  (ispRel_iff_witness X Y).mpr ⟨m, n, X', Y', ⟨wX⟩, ⟨wY⟩, ⟨F⟩⟩

end DiamondIntegral.Section7.Lemma714Witness
