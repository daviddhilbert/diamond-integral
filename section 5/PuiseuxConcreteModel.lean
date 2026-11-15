import «section 5».PuiseuxConcreteLanguage
import «section 5».PuiseuxAlgebraicClosedness
import Section6.ConcreteACVF

/-! The concrete Puiseux original-language structure satisfies ACVF(0,0).
Newton–Puiseux algebraic closedness, the actual valuation and its residue
field are all checked constructions; no model assertion is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section6

local instance sourceModelStructure : LRV.Structure (ConcreteValued.Carrier v) := ConcreteValued.nativeStructure v
local instance targetModelStructure : LRV.Structure Carrier := canonicalInterpret

theorem concrete_valuation_nontrivial : ∃ x : PuiseuxSeries ℂ, x ≠ 0 ∧ v x < 1 := by
  refine ⟨puiseuxMonomial 1 1,?_,?_⟩
  · intro h
    have he := congrArg (fun f : PuiseuxSeries ℂ => (f : HahnSeries ℚ ℂ)) h
    exact single_ne_zero (one_ne_zero : (1 : ℂ) ≠ 0) he
  · change (0 : WithTop ℚ) < (HahnSeries.single (1 : ℚ) (1 : ℂ)).orderTop
    simp [orderTop_single]

theorem canonical_model_ACVF00 : Carrier ⊨ Axioms.ACVF00 := by
  letI : CharZero (PuiseuxSeries ℂ) := charZero_of_injective_ringHom (puiseuxConstant (k := ℂ)).injective
  letI : IsAlgClosed (PuiseuxSeries ℂ) := puiseuxAlgebraicallyClosed ℂ
  letI : CharZero (ConcreteRV.Residue v) := charZero_of_injective_ringHom constantResidue.injective
  letI : ConcreteValued.Carrier v ⊨ Axioms.ACVF00 :=
    ConcreteValued.model_ACVF00 v concrete_valuation_nontrivial
  exact FirstOrder.Language.StrongHomClass.theory_model concreteLanguageEquiv

theorem canonical_model_ACVF : Carrier ⊨ Axioms.ACVF := by
  constructor
  intro σ hσ
  exact canonical_model_ACVF00.realize_of_mem σ (Or.inl (Or.inl hσ))

end DiamondIntegral.Section5.PuiseuxOriginal
