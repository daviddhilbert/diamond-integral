import «section 5».RESPositiveCombinations
import «section 5».RESStabilizationExpressions

/-! Actual finite tagged sums of positive RES expressions preserve
additive evaluations, including the absolute total-family evaluation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p n : ℕ} {sp : Fin p → SortTag}

theorem resExpressionListSum_additive_evaluate {R : Type*} [AddCommGroup R]
    (ev : FreeCommRing (RESAtomSchema B p sp) →+ R)
    (L : List ((a : ℕ) × RESExpressionSchema B p sp a)) :
    ev (resExpressionListSum L).2.formalValue = (L.map (fun E => ev E.2.formalValue)).sum := by
  induction L with
  | nil => exact ev.map_zero
  | cons E L ih =>
    change ev (E.2.formalValue + (resExpressionListSum L).2.formalValue) = _
    rw [ev.map_add,ih]
    rfl

def resExpressionFiniteSum (E : Fin n → (a : ℕ) × RESExpressionSchema B p sp a) :
    (a : ℕ) × RESExpressionSchema B p sp a := resExpressionListSum (List.ofFn E)

theorem resExpressionFiniteSum_valid
    (E : Fin n → (a : ℕ) × RESExpressionSchema B p sp a)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hv : ∀ i, (E i).2.Valid hc z) : (resExpressionFiniteSum E).2.Valid hc z := by
  apply resExpressionListSum_valid hc _ z hz
  intro F hF
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hF
  exact hv i

theorem resExpressionFiniteSum_additive_evaluate {R : Type*} [AddCommGroup R]
    (ev : FreeCommRing (RESAtomSchema B p sp) →+ R)
    (E : Fin n → (a : ℕ) × RESExpressionSchema B p sp a) :
    ev (resExpressionFiniteSum E).2.formalValue = ∑ i : Fin n, ev (E i).2.formalValue := by
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,resExpressionFiniteSum]
    using resExpressionListSum_additive_evaluate ev (List.ofFn E)

theorem resExpressionFiniteSum_native_value
    (E : Fin n → (a : ℕ) × RESExpressionSchema B p sp a)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hv : ∀ i, (E i).2.Valid hc z) :
    (resExpressionFiniteSum E).2.nativeValue hc z (resExpressionFiniteSum_valid E z hz hv) =
      ∑ i : Fin n, (E i).2.nativeValue hc z (hv i) := by
  have he := resExpressionFiniteSum_additive_evaluate (nativeSchemaEvaluator hc z).toAddMonoidHom E
  change nativeSchemaEvaluator hc z (resExpressionFiniteSum E).2.formalValue =
    ∑ i : Fin n, nativeSchemaEvaluator hc z (E i).2.formalValue at he
  rw [(resExpressionFiniteSum E).2.formalValue_evaluate hc z (resExpressionFiniteSum_valid E z hz hv)] at he
  exact he.trans (Finset.sum_congr rfl (fun i _ => (E i).2.formalValue_evaluate hc z (hv i)))

theorem integer_positive_negative_cast {R : Type*} [Ring R] (c : ℤ) :
    (c.toNat : R) - ((-c).toNat : R) = (c : R) := by
  have h := congrArg (Int.castRingHom R) (Int.toNat_sub_toNat_neg c)
  simpa only [map_sub,Int.coe_castRingHom,Int.cast_natCast] using h

theorem integer_positive_negative_weighted {R : Type*} [CommRing R] (c : ℤ) (x y : R) :
    (c.toNat : R) * (x*y) - ((-c).toNat : R) * (x*y) = x*(c : R)*y := by
  rw [←sub_mul,integer_positive_negative_cast]
  ring

end DiamondIntegral.Section5
