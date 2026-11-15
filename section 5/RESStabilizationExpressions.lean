import «section 5».RESRelationTermExpressions

/-! Finite sums of actual oriented relation expressions and the common
stabilizer give the two literal total domains of a native equality witness. -/
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
variable {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

def resExpressionListSum : List ((a : ℕ) × RESExpressionSchema B p sp a) → (a : ℕ) × RESExpressionSchema B p sp a
  | [] => ⟨0, .empty⟩
  | F :: L => let R := resExpressionListSum L; ⟨1+(F.1+R.1), .sum F.2 R.2⟩

theorem resExpressionListSum_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List ((a : ℕ) × RESExpressionSchema B p sp a)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ F ∈ L, F.2.Valid hc z) :
    (resExpressionListSum L).2.Valid hc z := by
  induction L with
  | nil => exact hz
  | cons F L ih => exact ⟨hL F List.mem_cons_self, ih (fun G hG => hL G (List.mem_cons_of_mem _ hG))⟩

def resRelationLeftExpression (L : List (RESRelationTermSchema B p sp)) :
    (a : ℕ) × RESExpressionSchema B p sp a := resExpressionListSum (L.map RESRelationTermSchema.leftExpression)
def resRelationRightExpression (L : List (RESRelationTermSchema B p sp)) :
    (a : ℕ) × RESExpressionSchema B p sp a := resExpressionListSum (L.map RESRelationTermSchema.rightExpression)

theorem resRelationLeftExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESRelationTermSchema B p sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ T ∈ L, T.Valid hc z) :
    (resRelationLeftExpression L).2.Valid hc z := by
  apply resExpressionListSum_valid hc _ z hz
  intro E hE
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hE
  exact T.leftExpression_valid hc z (hL T hT)

theorem resRelationRightExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESRelationTermSchema B p sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ T ∈ L, T.Valid hc z) :
    (resRelationRightExpression L).2.Valid hc z := by
  apply resExpressionListSum_valid hc _ z hz
  intro E hE
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hE
  exact T.rightExpression_valid hc z (hL T hT)

theorem resRelationExpressions_native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESRelationTermSchema B p sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ T ∈ L, T.Valid hc z) :
    (resRelationLeftExpression L).2.nativeValue hc z (resRelationLeftExpression_valid hc L z hz hL) =
    (resRelationRightExpression L).2.nativeValue hc z (resRelationRightExpression_valid hc L z hz hL) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    exact congrArg₂ (fun x y => x+y) (T.native_expression_equality hc z (hL T List.mem_cons_self))
      (ih (fun U hU => hL U (List.mem_cons_of_mem _ hU)))

def resStabilizedExpression (F : RESSetSchema B p a sp)
    (C : List ((a : ℕ) × RESSetSchema B p a sp)) (R : (a : ℕ) × RESExpressionSchema B p sp a) :
    (a : ℕ) × RESExpressionSchema B p sp a :=
  let S := resListExpression C
  ⟨1+(a+(1+(S.1+R.1))), .sum (.atom F) (.sum S.2 R.2)⟩

theorem resStabilizedExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RESSetSchema B p a sp) (C : List ((a : ℕ) × RESSetSchema B p a sp))
    (R : (a : ℕ) × RESExpressionSchema B p sp a) (z : Fin p → M)
    (hF : F.Valid hc z) (hC : ∀ G ∈ C, G.2.Valid hc z) (hR : R.2.Valid hc z) :
    (resStabilizedExpression F C R).2.Valid hc z :=
  ⟨hF, resListExpression_valid hc C z hF.1 hC, hR⟩

end DiamondIntegral.Section5
