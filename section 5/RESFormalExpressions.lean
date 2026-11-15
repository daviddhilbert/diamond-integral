import «section 5».RESExpressionRecoding

/-! Literal domain layouts carry formal polynomial values in their
schema leaves. Algebraic layout identities are separate from native relations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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

abbrev RESAtomSchema (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) :=
  (a : ℕ) × RESSetSchema B p a sp

def RESExpressionSchema.formalValue : {a : ℕ} → RESExpressionSchema B p sp a → FreeCommRing (RESAtomSchema B p sp)
  | _, .atom F => FreeCommRing.of ⟨_, F⟩
  | _, .empty => 0
  | _, .sum F G => F.formalValue + G.formalValue
  | _, .product F G => F.formalValue * G.formalValue

def nativeSchemaEvaluator (hc : CanonicalStructure.IsCanonical (M := M)) (z : Fin p → M) :
    FreeCommRing (RESAtomSchema B p sp) →+* RESDimensionFreeReduction.Ring ⟨B.real ∪ Set.range z, B.gamma⟩ :=
  FreeCommRing.lift (fun F => if h : F.2.Valid hc z then nativeRESChartClass (F.2.chart hc z h) else 0)

theorem RESExpressionSchema.formalValue_evaluate (hc : CanonicalStructure.IsCanonical (M := M))
    (E : RESExpressionSchema B p sp a) (z : Fin p → M) (h : E.Valid hc z) :
    nativeSchemaEvaluator hc z E.formalValue = E.nativeValue hc z h := by
  induction E with
  | atom F =>
    have hF : F.Valid hc z := h
    change nativeSchemaEvaluator hc z (FreeCommRing.of (⟨_, F⟩ : RESAtomSchema B p sp)) = _
    exact (FreeCommRing.lift_of
      (fun A : RESAtomSchema B p sp => if hA : A.2.Valid hc z then nativeRESChartClass (A.2.chart hc z hA) else 0)
      (⟨_, F⟩ : RESAtomSchema B p sp)).trans (dif_pos hF)
  | empty => exact map_zero _
  | sum F G ihF ihG =>
    change nativeSchemaEvaluator hc z (F.formalValue + G.formalValue) = _
    rw [map_add, ihF h.1, ihG h.2]
    rfl
  | product F G ihF ihG =>
    change nativeSchemaEvaluator hc z (F.formalValue * G.formalValue) = _
    rw [map_mul, ihF h.1, ihG h.2]
    rfl

end DiamondIntegral.Section5
