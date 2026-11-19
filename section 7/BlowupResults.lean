import «section 7».BlowupCongruence
import «section 7».ElementaryComparison

/-! Unconditional forms of Lemma 7.5 through Lemma 7.10 (additive part), on
isomorphism classes of `μRV^db[1+k]`, over an arbitrary parameter base.

Lemma 7.5 (`ElementaryComparison.elementaryDiamond`) discharges the hypothesis
`ElementaryDiamond B k` of `BlowupCongruence`; the statements below take no
input beyond the ACVF model. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.BlowupResults
open DiamondIntegral.Section4 DiamondIntegral.Section4.RelativeAnnularGenerators DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryComparison

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-- Lemma 7.5 (`elementary:blowups:preserves:iso:vol`). -/
theorem lemma_7_5 (D E : AnnularDatum B k) (h : Nonempty (Iso D.source.toChart E.source.toChart)) :
    ∃ w : Cls B (1 + k), Step (cls D.annularObject) w ∧ Step (cls E.annularObject) w :=
  ElementaryComparison.lemma_7_5 D E h

/-- Corollary 7.6 (`eblowup:same:loci:iso`): two blowups of length one of
isomorphic objects have blowups of length one with isomorphic results. -/
theorem corollary_7_6 {x y y' : Cls B (1 + k)} (h₁ : Step x y) (h₂ : Step x y') :
    ∃ w, Step y w ∧ Step y' w :=
  step_diamond elementaryDiamond h₁ h₂

/-- Lemma 7.7 (`blowup:equi:class:coa`). -/
theorem lemma_7_7 {x x₁ y₁ : Cls B (1 + k)} {m n : ℕ}
    (h₁ : BlowupSteps m x x₁) (h₂ : BlowupSteps n x y₁) :
    ∃ w, BlowupSteps n x₁ w ∧ BlowupSteps m y₁ w :=
  BlowupCongruence.lemma_7_7 elementaryDiamond h₁ h₂

/-- Corollary 7.8 (`blowup:equi:class`). -/
theorem corollary_7_8 {U U' V V' : Obj B (1 + k)} (hU : Nonempty (Iso U.toChart U'.toChart))
    (hV : Nonempty (Iso V.toChart V'.toChart)) (h : MuIsp (cls U) (cls V)) : MuIsp (cls U') (cls V') :=
  BlowupCongruence.corollary_7_8 (cls_eq_iff.mpr hU) (cls_eq_iff.mpr hV) h

/-- Lemma 7.10 (`isp:congruence:vol`), additive part: `μIsp^db[1+k]` is a
congruence of the semigroup of isomorphism classes. -/
def lemma_7_10_addCon : AddCon (Cls B (1 + k)) := muIspAddCon elementaryDiamond

theorem lemma_7_10_addCon_iff (x y : Cls B (1 + k)) : lemma_7_10_addCon x y ↔ MuIsp x y := Iff.rfl

theorem muIsp_transitive {x y z : Cls B (1 + k)} (h₁ : MuIsp x y) (h₂ : MuIsp y z) : MuIsp x z :=
  muIsp_trans elementaryDiamond h₁ h₂

end DiamondIntegral.Section7.BlowupResults
