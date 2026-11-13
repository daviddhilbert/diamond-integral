import «section 3».RVUnitValueHom
import Section3.GammaDefinableClosureField
import Mathlib.GroupTheory.QuotientGroup.Basic
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The original-ground definable nonzero RV points form an actual
subgroup. Gamma names do not supply extra representatives by fiat. -/
def gammaGroundRVDefinableUnits (B : Base (M := M)) :
    Subgroup (CanonicalRV.RVSort M)ˣ where
  carrier u := DefinableClosureAtBase B .rv u.val.val
  one_mem' := by
    change DefinableClosureAtBase B .rv (1 : CanonicalRV.RVSort M).val
    rw [RVOperations.one_val]
    exact definableClosureAtBase_function_symbol B Fn.rvOne Fin.elim0
      (fun i => i.elim0) (fun i => i.elim0)
  mul_mem' := by
    intro a b ha hb
    change DefinableClosureAtBase B .rv (a.val*b.val).val
    rw [RVOperations.mul_val]
    exact definableClosureAtBase_function_symbol B Fn.rvMul ![a.val.val,b.val.val]
      (by intro i; fin_cases i; exact a.val.property; exact b.val.property)
      (by intro i; fin_cases i; exact ha; exact hb)
  inv_mem' := by
    intro a ha
    change DefinableClosureAtBase B .rv (a⁻¹).val.val
    rw [Units.val_inv_eq_inv_val,RVOperations.inv_val]
    exact definableClosureAtBase_function_symbol B Fn.rvInv ![a.val.val]
      (by intro i; fin_cases i; exact a.val.property)
      (by intro i; fin_cases i; exact ha)

def gammaGroundDefinableRVValues (B : Base (M := M)) :
    Subgroup (Values.Gamma (M := M)) :=
  (gammaGroundRVDefinableUnits B).map rvUnitValueHom

theorem gammaGroundDefinableRVValues_mem_iff (B : Base (M := M))
    (γ : Values.Gamma (M := M)) :
    γ ∈ gammaGroundDefinableRVValues B ↔
      ∃ c : (CanonicalRV.RVSort M)ˣ,
        DefinableClosureAtBase B .rv c.val.val ∧ rvUnitValueHom c = γ := Iff.rfl

end DiamondIntegral.Section3
