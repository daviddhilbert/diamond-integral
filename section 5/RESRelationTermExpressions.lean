import «section 5».RESPrimitiveExpressions
import «section 5».RESRelationTermSchemata

/-! Coefficient families and oriented primitive relations form literal
native expressions. Their equality follows from the actual primitive law. -/
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
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

def resListExpression : List ((a : ℕ) × RESSetSchema B p a sp) → (a : ℕ) × RESExpressionSchema B p sp a
  | [] => ⟨0, .empty⟩
  | F :: L => let R := resListExpression L; ⟨1+(F.1+R.1), .sum (.atom F.2) R.2⟩

theorem resListExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List ((a : ℕ) × RESSetSchema B p a sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ F ∈ L, F.2.Valid hc z) :
    (resListExpression L).2.Valid hc z := by
  induction L with
  | nil => exact hz
  | cons F L ih => exact ⟨hL F List.mem_cons_self, ih (fun G hG => hL G (List.mem_cons_of_mem _ hG))⟩

def RESRelationTermSchema.leftExpression (T : RESRelationTermSchema B p sp) :
    (a : ℕ) × RESExpressionSchema B p sp a :=
  let C := resListExpression T.coefficients
  let P := if T.reversed then T.primitive.rightExpression else T.primitive.leftExpression
  ⟨P.1+C.1, .product C.2 P.2⟩

def RESRelationTermSchema.rightExpression (T : RESRelationTermSchema B p sp) :
    (a : ℕ) × RESExpressionSchema B p sp a :=
  let C := resListExpression T.coefficients
  let P := if T.reversed then T.primitive.leftExpression else T.primitive.rightExpression
  ⟨P.1+C.1, .product C.2 P.2⟩

theorem RESRelationTermSchema.leftExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (T : RESRelationTermSchema B p sp) (z : Fin p → M) (h : T.Valid hc z) :
    T.leftExpression.2.Valid hc z := by
  rcases T with ⟨P, C, r⟩
  have hz := (P.valid_definable hc).proper z h.1
  have hC := resListExpression_valid hc C z hz h.2
  cases r
  · exact ⟨hC, P.leftExpression_valid hc z h.1⟩
  · exact ⟨hC, P.rightExpression_valid hc z h.1⟩

theorem RESRelationTermSchema.rightExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (T : RESRelationTermSchema B p sp) (z : Fin p → M) (h : T.Valid hc z) :
    T.rightExpression.2.Valid hc z := by
  rcases T with ⟨P, C, r⟩
  have hz := (P.valid_definable hc).proper z h.1
  have hC := resListExpression_valid hc C z hz h.2
  cases r
  · exact ⟨hC, P.rightExpression_valid hc z h.1⟩
  · exact ⟨hC, P.leftExpression_valid hc z h.1⟩

theorem RESRelationTermSchema.native_expression_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (T : RESRelationTermSchema B p sp) (z : Fin p → M) (h : T.Valid hc z) :
    T.leftExpression.2.nativeValue hc z (T.leftExpression_valid hc z h) =
      T.rightExpression.2.nativeValue hc z (T.rightExpression_valid hc z h) := by
  rcases T with ⟨P, C, r⟩
  have hp := P.native_expression_equality hc z h.1
  have hz := (P.valid_definable hc).proper z h.1
  let c := (resListExpression C).2.nativeValue hc z (resListExpression_valid hc C z hz h.2)
  cases r
  · exact congrArg (fun x => c*x) hp
  · exact congrArg (fun x => c*x) hp.symm

end DiamondIntegral.Section5
