import Integration7.FrozenGenericCoefficientFields

/-! A generic frozen prefix and an independent unary fibre point give
an independent full tuple over the original VF parameter field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3

theorem independent_frozen_prefix_append {K : Type} [Field K] {n p : ℕ}
    (E : Subfield K) (x : Fin n → K) (z : Fin p → K)
    (hx : AlgebraicIndependent E x) (hz : AlgebraicIndependent (tupleField E x) z) :
    AlgebraicIndependent E (Fin.append x z) := by
  have h := independent_append_over_tuple_field E x z hx hz
  convert h.comp (finAddFlip : Fin (n+p) → Fin (p+n)) finAddFlip.injective using 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply,finAddFlip_apply_castAdd,finAddFlip_apply_natAdd,Fin.append_left,Fin.append_right]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : GammaParameters.Base (M := M)} {n p : ℕ}

theorem gammaFrozenPrefix_independent (x : Fin n → VFType (M := M)) (z : Fin p → VFType (M := M))
    (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (hz : AlgebraicIndependent (vfParameterField (B.real ∪ Set.range (vfValues x))) z) :
    AlgebraicIndependent (vfParameterField B.real) (Fin.append x z) := by
  have hz' : AlgebraicIndependent (tupleField (vfParameterField B.real) x) z :=
    Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E z)
      (vfParameterField_union_tuple B.real x)) hz
  exact independent_frozen_prefix_append (vfParameterField B.real) x z hx hz'

end DiamondIntegral.Section3
