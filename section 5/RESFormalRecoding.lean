import «section 5».RESFormalExpressions

/-! Formal layout identities transport by the ring homomorphism induced
by literal leaf recoding. No native quotient relation is used here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def formalSchemaRecode (R : GammaParameterRecode B p q sp sq) :
    FreeCommRing (RESAtomSchema B p sp) →+* FreeCommRing (RESAtomSchema B q sq) :=
  FreeCommRing.lift (fun A => FreeCommRing.of ⟨A.1, A.2.recode R⟩)

theorem RESExpressionSchema.formalValue_recode (R : GammaParameterRecode B p q sp sq)
    (E : RESExpressionSchema B p sp a) :
    (E.recode R).formalValue = formalSchemaRecode R E.formalValue := by
  induction E with
  | atom F => simp only [recode, formalValue, formalSchemaRecode, FreeCommRing.lift_of]
  | empty => exact (map_zero _).symm
  | sum F G ihF ihG =>
    change (F.recode R).formalValue + (G.recode R).formalValue = formalSchemaRecode R (F.formalValue+G.formalValue)
    rw [map_add, ihF, ihG]
  | product F G ihF ihG =>
    change (F.recode R).formalValue * (G.recode R).formalValue = formalSchemaRecode R (F.formalValue*G.formalValue)
    rw [map_mul, ihF, ihG]

end DiamondIntegral.Section5
