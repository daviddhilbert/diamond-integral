import «section 7».ElementaryBlowups
import HilbertMathlib.Foundation.Rewriting.Iteration

/-! Lemma 7.7 (`blowup:equi:class:coa`), Corollary 7.8 (`blowup:equi:class`),
Definition 7.9 (`μIsp^db`) and the additive part of Lemma 7.10
(`isp:congruence:vol`), on isomorphism classes of `μRV^db[1+k]`.

Each result here is proved from the one-step diamond, Corollary 7.6
(`ElementaryBlowups.step_diamond`), which in turn uses Lemma 7.5 through the
hypothesis `ElementaryDiamond B k`. That hypothesis is discharged by
`ElementaryComparison.elementaryDiamond`; the unconditional forms are stated
there. The finite grid argument is the generic `Iteration.grid` of
hilbert-mathlib (the combinatorial part of [Yin, Lemmas 6.5 and 6.8]); it takes
the geometric diamond as an explicit premise and hides no Section 7 conclusion.

`Steps n x y` is a blowup chain of length exactly `n` (empty loci allowed), and
`μIsp` is the existence of blowup chains of `x` and `y` with a common class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section4
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-- Blowup chains of length `n` on classes (Definition 7.2, "an annular blowup of
length `n` is a composition of `n` annular blowups"). -/
abbrev BlowupSteps (n : ℕ) (x y : Cls B (1 + k)) : Prop := Steps Step n x y

/-- Definition 7.9: `(x, y) ∈ μIsp^db[1+k]` when `x` and `y` have blowups with a
common class. -/
def MuIsp (x y : Cls B (1 + k)) : Prop := Common Step x y

/-- Corollary 7.6 as an `Iteration.Diamond`. -/
theorem diamond (hE : ElementaryDiamond B k) : Diamond (Step (B := B) (k := k)) :=
  fun h₁ h₂ => step_diamond hE h₁ h₂

/-- Lemma 7.7: if `[U] = [V]` and `U₁`, `V₁` are blowups of `U`, `V` of lengths
`m`, `n`, then there are blowups of `U₁`, `V₁` of lengths `n`, `m` with equal
classes. -/
theorem lemma_7_7 (hE : ElementaryDiamond B k) {x x₁ y₁ : Cls B (1 + k)} {m n : ℕ}
    (h₁ : BlowupSteps m x x₁) (h₂ : BlowupSteps n x y₁) :
    ∃ w, BlowupSteps n x₁ w ∧ BlowupSteps m y₁ w :=
  grid (diamond hE) h₁ h₂

/-- Corollary 7.8: if `[U] = [U']`, `[V] = [V']` and `U`, `V` have blowups with a
common class, then so do `U'`, `V'`. -/
theorem corollary_7_8 {U U' V V' : Obj B (1 + k)} (hU : cls U = cls U') (hV : cls V = cls V')
    (h : MuIsp (cls U) (cls V)) : MuIsp (cls U') (cls V') := by
  rw [← hU, ← hV]
  exact h

theorem muIsp_refl (x : Cls B (1 + k)) : MuIsp x x := Common.refl x

theorem muIsp_symm {x y : Cls B (1 + k)} (h : MuIsp x y) : MuIsp y x := Common.symm h

theorem muIsp_trans (hE : ElementaryDiamond B k) {x y z : Cls B (1 + k)}
    (h₁ : MuIsp x y) (h₂ : MuIsp y z) : MuIsp x z :=
  Common.trans (diamond hE) h₁ h₂

theorem steps_add_left (w : Cls B (1 + k)) {n : ℕ} {x y : Cls B (1 + k)}
    (h : BlowupSteps n x y) : BlowupSteps n (w + x) (w + y) := by
  induction h with
  | refl a => exact .refl _
  | cons h _ ih => exact .cons (step_add_left w h) ih

theorem steps_add_right (w : Cls B (1 + k)) {n : ℕ} {x y : Cls B (1 + k)}
    (h : BlowupSteps n x y) : BlowupSteps n (x + w) (y + w) := by
  simpa only [add_comm _ w] using steps_add_left w h

theorem steps_add {m n : ℕ} {x y x' y' : Cls B (1 + k)} (h : BlowupSteps m x y)
    (h' : BlowupSteps n x' y') : BlowupSteps (m + n) (x + x') (y + y') :=
  Steps.trans (steps_add_right x' h) (steps_add_left y h')

theorem muIsp_add {x y x' y' : Cls B (1 + k)} (h : MuIsp x y) (h' : MuIsp x' y') :
    MuIsp (x + x') (y + y') := by
  obtain ⟨c, m, n, hx, hy⟩ := h
  obtain ⟨c', m', n', hx', hy'⟩ := h'
  exact ⟨c + c', m + m', n + n', steps_add hx hx', steps_add hy hy'⟩

/-- Lemma 7.10, additive part: `μIsp^db[1+k]` is a congruence of the semigroup of
isomorphism classes. -/
def muIspAddCon (hE : ElementaryDiamond B k) : AddCon (Cls B (1 + k)) where
  r := MuIsp
  iseqv := ⟨muIsp_refl, muIsp_symm, muIsp_trans hE⟩
  add' := muIsp_add

theorem muIspAddCon_iff (hE : ElementaryDiamond B k) (x y : Cls B (1 + k)) :
    muIspAddCon hE x y ↔ MuIsp x y := Iff.rfl

end DiamondIntegral.Section7.BlowupCongruence
