import Section3.RVOperations
import «section 3».IntegerMonomialMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvUnitValueHom : (CanonicalRV.RVSort M)ˣ →* Values.Gamma (M := M) where
  toFun t := Values.gammaOf t.val (fun h => Units.ne_zero t (Subtype.ext (h.trans RVOperations.zero_val.symm)))
  map_one' := by
    apply Subtype.ext
    change Values.vrv (1 : CanonicalRV.RVSort M) = (1 : Values.Gamma (M := M)).val
    rw [Values.gamma_val_one]
    have ho : (1 : CanonicalRV.RVSort M) = CanonicalRV.encodedRv (1 : VFType (M := M)) :=
      (map_one RVOperations.rvHom).symm
    rw [ho]
    exact Values.vf_value_one
  map_mul' t u := by
    apply Subtype.ext
    change Values.vrv ((t : CanonicalRV.RVSort M) * (u : CanonicalRV.RVSort M)) = _
    rw [Values.gamma_val_mul]
    have hm : (t : CanonicalRV.RVSort M) * (u : CanonicalRV.RVSort M) =
        ⟨iRVMul (t : CanonicalRV.RVSort M).val (u : CanonicalRV.RVSort M).val,
          rv_mul_mem (inferInstance : M ⊨ Axioms.ACVF) t.val.property u.val.property⟩ :=
      Subtype.ext (RVOperations.mul_val _ _)
    rw [hm,Values.vrv_mul]
    rfl

theorem monomial_map_value {ι G Γ : Type} [Fintype ι] [CommGroup G] [CommGroup Γ]
    (v : G →* Γ) (A : Matrix ι ι ℤ) (x : ι → G) :
    (fun i => v (integerMonomialMap A x i)) = integerMonomialMap A (fun i => v (x i)) := by
  funext i
  simp only [integerMonomialMap,map_prod,map_zpow]
end DiamondIntegral.Section3
