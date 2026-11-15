import «section 5».RESExpressionBijections
import «section 5».GammaValueNativeFibres

/-! Actual native RES relation certificates are stable under arbitrary
finite coefficient expressions and reversal. A fibre pair uses two full
value torsors; both classes are proved equal to the same residue torus. -/
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
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

inductive RESExpressionRelationSchema (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) : ℕ → ℕ → Type where
  | underlying {a b : ℕ} (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
      (graph : RESBijectionSchema F G) : RESExpressionRelationSchema B p sp a b
  | fibre (F G : GammaValueSchema B p sp) : RESExpressionRelationSchema B p sp 1 1
  | reverse {a b : ℕ} (R : RESExpressionRelationSchema B p sp a b) : RESExpressionRelationSchema B p sp b a
  | multiplyLeft {a b c : ℕ} (C : RESExpressionSchema B p sp c)
      (R : RESExpressionRelationSchema B p sp a b) : RESExpressionRelationSchema B p sp (a+c) (b+c)

mutual
def RESExpressionRelationSchema.leftExpression : {a b : ℕ} → RESExpressionRelationSchema B p sp a b →
      RESExpressionSchema B p sp a
    | _, _, .underlying F _ _ => .atom F
    | _, _, .fibre F _ => .atom F.resSchema
    | _, _, .reverse R => R.rightExpression
    | _, _, .multiplyLeft C R => .product C R.leftExpression

def RESExpressionRelationSchema.rightExpression : {a b : ℕ} → RESExpressionRelationSchema B p sp a b →
      RESExpressionSchema B p sp b
    | _, _, .underlying _ G _ => .atom G
    | _, _, .fibre _ G => .atom G.resSchema
    | _, _, .reverse R => R.leftExpression
    | _, _, .multiplyLeft C R => .product C R.rightExpression
end

def RESExpressionRelationSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M)) :
    {a b : ℕ} → RESExpressionRelationSchema B p sp a b → (Fin p → M) → Prop
  | _, _, .underlying _ _ H, z => H.Valid hc z
  | _, _, .fibre F G, z => F.Valid hc z ∧ G.Valid hc z
  | _, _, .reverse R, z => R.Valid hc z
  | _, _, .multiplyLeft C R, z => C.Valid hc z ∧ R.Valid hc z

theorem RESExpressionRelationSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (R : RESExpressionRelationSchema B p sp a b) : DefinableOverBase B sp {z | R.Valid hc z} := by
  induction R with
  | underlying F G H => exact H.valid_definable hc
  | fibre F G => exact (F.valid_definable hc).inter (G.valid_definable hc)
  | reverse R ih => exact ih
  | multiplyLeft C R ih => exact (C.valid_definable hc).inter ih

theorem RESExpressionRelationSchema.expressions_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (R : RESExpressionRelationSchema B p sp a b) (z : Fin p → M) (h : R.Valid hc z) :
    R.leftExpression.Valid hc z ∧ R.rightExpression.Valid hc z := by
  induction R with
  | underlying F G H => exact ⟨h.1, h.2.1⟩
  | fibre F G => exact ⟨h.1.1, h.2.1⟩
  | reverse R ih => exact ⟨(ih h).2, (ih h).1⟩
  | multiplyLeft C R ih => exact ⟨⟨h.1, (ih h.2).1⟩, h.1, (ih h.2).2⟩

theorem RESExpressionRelationSchema.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (R : RESExpressionRelationSchema B p sp a b) (z : Fin p → M) (h : R.Valid hc z) :
    R.leftExpression.nativeValue hc z (R.expressions_valid hc z h).1 =
      R.rightExpression.nativeValue hc z (R.expressions_valid hc z h).2 := by
  induction R with
  | underlying F G H => exact H.native_equality hc z h
  | fibre F G => exact (F.native_fibre_equality hc z h.1).trans (G.native_fibre_equality hc z h.2).symm
  | reverse R ih => exact (ih h).symm
  | multiplyLeft C R ih => exact congrArg (fun x => C.nativeValue hc z h.1 * x) (ih h.2)

end DiamondIntegral.Section5
