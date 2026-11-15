import «section 5».RESExpressionSchemata
import «section 5».RESPrimitiveSchemata
import «section 5».GammaConstantValueSchemata

/-! Every primitive native ideal witness supplies two literal finite
RES expressions with equal actual native values. -/
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

def RESPrimitiveSchema.leftExpression : RESPrimitiveSchema B p sp →
    (a : ℕ) × RESExpressionSchema B p sp a
  | .underlying F _ _ => ⟨_, .atom F⟩
  | .fibre F => ⟨1, .atom F.resSchema⟩

def RESPrimitiveSchema.rightExpression : RESPrimitiveSchema B p sp →
    (a : ℕ) × RESExpressionSchema B p sp a
  | .underlying _ G _ => ⟨_, .atom G⟩
  | .fibre _ => ⟨1, .atom (nativeTorusSchema B sp)⟩

theorem RESPrimitiveSchema.leftExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (P : RESPrimitiveSchema B p sp) (z : Fin p → M) (h : P.Valid hc z) :
    P.leftExpression.2.Valid hc z := by
  cases P with
  | underlying F G H => exact h.1
  | fibre F => exact h.1

theorem RESPrimitiveSchema.rightExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (P : RESPrimitiveSchema B p sp) (z : Fin p → M) (h : P.Valid hc z) :
    P.rightExpression.2.Valid hc z := by
  have hz := (P.valid_definable hc).proper z h
  cases P with
  | underlying F G H => exact h.2.1
  | fibre F =>
    exact (GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) z hz).1

theorem RESPrimitiveSchema.native_expression_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (P : RESPrimitiveSchema B p sp) (z : Fin p → M) (h : P.Valid hc z) :
    P.leftExpression.2.nativeValue hc z (P.leftExpression_valid hc z h) =
      P.rightExpression.2.nativeValue hc z (P.rightExpression_valid hc z h) := by
  have hz := (P.valid_definable hc).proper z h
  cases P with
  | underlying F G H => exact H.native_equality hc z h
  | fibre F =>
    let T : GammaValueSchema B p sp := GammaValueSchema.constant 1 (GammaGroupNames.one_definable_base B)
    have hT := GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) z hz
    exact (F.native_fibre_equality hc z h).trans (T.native_fibre_equality hc z hT).symm

end DiamondIntegral.Section5
