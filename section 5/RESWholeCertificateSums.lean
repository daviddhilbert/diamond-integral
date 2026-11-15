import «section 5».RESWholeRelationCertificates

/-! Finite whole-expression certificates have exact formal sums,
native equality and unchanged recoding identities. -/
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
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def resWholeLeftPolynomial (L : List (RESWholeRelationCertificate B p sp)) :
    FreeCommRing (RESAtomSchema B p sp) := (L.map (fun C => C.leftExpression.2.formalValue)).sum

def resWholeRightPolynomial (L : List (RESWholeRelationCertificate B p sp)) :
    FreeCommRing (RESAtomSchema B p sp) := (L.map (fun C => C.rightExpression.2.formalValue)).sum

theorem RESWholeRelationCertificate.native_formal_equality
    (hc : CanonicalStructure.IsCanonical (M := M))
    (C : RESWholeRelationCertificate B p sp) (z : Fin p → M) (hv : C.Valid hc z) :
    nativeSchemaEvaluator hc z C.leftExpression.2.formalValue =
      nativeSchemaEvaluator hc z C.rightExpression.2.formalValue :=
  (C.leftExpression.2.formalValue_evaluate hc z (C.expressions_valid hc z hv).1).trans
    ((C.native_equality hc z hv).trans
      (C.rightExpression.2.formalValue_evaluate hc z (C.expressions_valid hc z hv).2).symm)

theorem resWholePolynomials_native_equality
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESWholeRelationCertificate B p sp)) (z : Fin p → M)
    (hv : ∀ C ∈ L, C.Valid hc z) :
    nativeSchemaEvaluator hc z (resWholeLeftPolynomial L) =
      nativeSchemaEvaluator hc z (resWholeRightPolynomial L) := by
  induction L with
  | nil => rfl
  | cons C L ih =>
    change nativeSchemaEvaluator hc z (C.leftExpression.2.formalValue+resWholeLeftPolynomial L) =
      nativeSchemaEvaluator hc z (C.rightExpression.2.formalValue+resWholeRightPolynomial L)
    rw [map_add,map_add]
    exact congrArg₂ (fun x y => x+y) (C.native_formal_equality hc z (hv C List.mem_cons_self))
      (ih (fun D hD => hv D (List.mem_cons_of_mem _ hD)))

theorem resWholeLeftPolynomial_recode
    (R : GammaParameterRecode B p q sp sq) (L : List (RESWholeRelationCertificate B p sp)) :
    resWholeLeftPolynomial (L.map (RESWholeRelationCertificate.recode R)) =
      formalSchemaRecode R (resWholeLeftPolynomial L) := by
  induction L with
  | nil => exact (map_zero _).symm
  | cons C L ih =>
    change (C.recode R).leftExpression.2.formalValue +
      resWholeLeftPolynomial (L.map (RESWholeRelationCertificate.recode R)) =
      formalSchemaRecode R (C.leftExpression.2.formalValue+resWholeLeftPolynomial L)
    rw [C.left_formal_recode R,ih,map_add]

theorem resWholeRightPolynomial_recode
    (R : GammaParameterRecode B p q sp sq) (L : List (RESWholeRelationCertificate B p sp)) :
    resWholeRightPolynomial (L.map (RESWholeRelationCertificate.recode R)) =
      formalSchemaRecode R (resWholeRightPolynomial L) := by
  induction L with
  | nil => exact (map_zero _).symm
  | cons C L ih =>
    change (C.recode R).rightExpression.2.formalValue +
      resWholeRightPolynomial (L.map (RESWholeRelationCertificate.recode R)) =
      formalSchemaRecode R (C.rightExpression.2.formalValue+resWholeRightPolynomial L)
    rw [C.right_formal_recode R,ih,map_add]

end DiamondIntegral.Section5
