import «section 5».RVRectanglePositiveExpressions
import «section 5».RESFormalRecoding

/-! Positive rectangle expressions have literal formal polynomial
certificates. These certificates recode without identifying parameter
bases or quotient classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem resExpressionCopies_formal_value (E : RESExpressionSchema B p sp a) (n : ℕ) :
    (resExpressionCopies E n).2.formalValue = (n : FreeCommRing (RESAtomSchema B p sp))*E.formalValue := by
  induction n with
  | zero => simp only [resExpressionCopies,RESExpressionSchema.formalValue,Nat.cast_zero,zero_mul]
  | succ n ih =>
    change E.formalValue + (resExpressionCopies E n).2.formalValue = _
    rw [ih,Nat.cast_succ,add_mul,one_mul,add_comm]

theorem resExpressionTorusTimes_formal_value (E : RESExpressionSchema B p sp a) (n : ℕ) :
    (resExpressionTorusTimes E n).2.formalValue =
      E.formalValue * FreeCommRing.of ⟨1,nativeTorusSchema B sp⟩ ^ n := by
  induction n with
  | zero => exact (mul_one _).symm
  | succ n ih =>
    change (resExpressionTorusTimes E n).2.formalValue * FreeCommRing.of ⟨1,nativeTorusSchema B sp⟩ = _
    rw [ih,pow_succ,mul_assoc]

theorem RVRectanglePieceSchema.resContribution_formal_value
    (F : RVRectanglePieceSchema B p a sp) (m : ℕ) :
    (F.resContribution m).2.formalValue = (m : FreeCommRing (RESAtomSchema B p sp)) *
      (FreeCommRing.of ⟨F.residueArity,F.residue⟩ * FreeCommRing.of ⟨1,nativeTorusSchema B sp⟩ ^ F.freeArity) := by
  unfold resContribution
  rw [resExpressionCopies_formal_value,resExpressionTorusTimes_formal_value]
  rfl

def RVRectangleDecompositionSchema.resPolynomial {D : GammaDomainFormula B p a sp}
    (W : RVRectangleDecompositionSchema D) (T : RESSetSchema B p 1 sp) (c : Fin W.size → ℕ) :
    FreeCommRing (RESAtomSchema B p sp) :=
  ∑ i : Fin W.size, (c i : FreeCommRing (RESAtomSchema B p sp)) *
    (FreeCommRing.of ⟨(W.cells i).residueArity,(W.cells i).residue⟩ * FreeCommRing.of ⟨1,T⟩ ^ (W.cells i).freeArity)

theorem RVRectangleDecompositionSchema.positiveExpression_formal
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind) :
    (W.positiveExpression hc kind).2.formalValue =
      W.resPolynomial (nativeTorusSchema B sp) (fun i => (((W.cells i).euler.syntax hc).eulerValue kind).toNat) := by
  have h := resExpressionFiniteSum_additive_evaluate
    (AddMonoidHom.id (FreeCommRing (RESAtomSchema B p sp)))
    (fun i => (W.cells i).resContribution (((W.cells i).euler.syntax hc).eulerValue kind).toNat)
  change (W.positiveExpression hc kind).2.formalValue = ∑ i : Fin W.size, _ at h
  exact h.trans (Finset.sum_congr rfl (fun i _ => (W.cells i).resContribution_formal_value _))

theorem RVRectangleDecompositionSchema.negativeExpression_formal
    {D : GammaDomainFormula B p a sp} (W : RVRectangleDecompositionSchema D)
    (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind) :
    (W.negativeExpression hc kind).2.formalValue =
      W.resPolynomial (nativeTorusSchema B sp) (fun i => (-((W.cells i).euler.syntax hc).eulerValue kind).toNat) := by
  have h := resExpressionFiniteSum_additive_evaluate
    (AddMonoidHom.id (FreeCommRing (RESAtomSchema B p sp)))
    (fun i => (W.cells i).resContribution (-((W.cells i).euler.syntax hc).eulerValue kind).toNat)
  change (W.negativeExpression hc kind).2.formalValue = ∑ i : Fin W.size, _ at h
  exact h.trans (Finset.sum_congr rfl (fun i _ => (W.cells i).resContribution_formal_value _))

theorem RVRectangleDecompositionSchema.resPolynomial_recode
    (R : GammaParameterRecode B p q sp sq) {D : GammaDomainFormula B p a sp}
    (W : RVRectangleDecompositionSchema D) (T : RESSetSchema B p 1 sp) (c : Fin W.size → ℕ) :
    formalSchemaRecode R (W.resPolynomial T c) = (W.recode R).resPolynomial (T.recode R) c := by
  unfold resPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul,map_natCast,map_pow]
  simp only [formalSchemaRecode,FreeCommRing.lift_of]
  rfl

end DiamondIntegral.Section5
