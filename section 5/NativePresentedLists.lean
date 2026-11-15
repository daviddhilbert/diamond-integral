import «section 5».NativeDegreePresentations
import «section 5».NativeSchemaPresentations
import «section 5».RESCertificateRecoding

/-! Every finite old native-object list has original-base presented
occurrences. Their products retain each old object and formal coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RESFiniteWitness
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

theorem native_presented_list_exists (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (L : List (GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩)) :
    ∃ P : List (PresentedGradedRESObjectAt (hc := hc) B sp z), presentedOldObjects P = L := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons U L ih =>
    obtain ⟨F, hF, _, ⟨f⟩⟩ := native_res_schema_at_parameter B sp z hz U.2
    obtain ⟨P, hP⟩ := ih
    let Q : NativeDomainPresentationAt B sp z U.2.obj.domain := ⟨U.2.obj.arity, .atom F, hF, f⟩
    exact ⟨⟨U, Q⟩ :: P, congrArg (List.cons U) hP⟩

def presentedFormalSum {z : Fin p → M} (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    FreeCommRing (RESAtomSchema B p sp) := (L.map (fun U => U.2.expression.formalValue)).sum

def presentedCoefficientExpression {z : Fin p → M} (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    (a : ℕ) × RESExpressionSchema B p sp a :=
  resExpressionListSum (L.map (fun U => ⟨U.2.arity, U.2.expression⟩))

theorem presentedCoefficientExpression_valid {z : Fin p → M}
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) (hz : ∀ i, sortEval (sp i) (z i)) :
    (presentedCoefficientExpression L).2.Valid hc z := by
  apply resExpressionListSum_valid hc _ z hz
  intro E hE
  obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hE
  exact U.2.valid

theorem presentedCoefficientExpression_formal {z : Fin p → M}
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    (presentedCoefficientExpression L).2.formalValue = presentedFormalSum L := by
  rw [presentedCoefficientExpression, resExpressionListSum_formal]
  simp only [List.map_map, Function.comp_def, presentedFormalSum]

def presentedProductList {z : Fin p → M}
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z))
    (U : GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩) (P : NativeDomainPresentationAt B sp z U.2.obj.domain) :
    List (PresentedGradedRESObjectAt (hc := hc) B sp z) :=
  L.map (fun V => ⟨gradedObjectProduct hc _ V.1 U, V.2.product z P⟩)

theorem presentedProductList_old {z : Fin p → M}
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z))
    (U : GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩) (P : NativeDomainPresentationAt B sp z U.2.obj.domain) :
    presentedOldObjects (presentedProductList L U P) = positiveFamilyProduct hc _ (presentedOldObjects L) [U] := by
  induction L with
  | nil => rfl
  | cons V L ih =>
    change gradedObjectProduct hc _ V.1 U :: presentedOldObjects (presentedProductList L U P) =
      gradedObjectProduct hc _ V.1 U :: positiveFamilyProduct hc _ (presentedOldObjects L) [U]
    exact congrArg (List.cons _) ih

theorem presentedProductList_formal {z : Fin p → M}
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z))
    (U : GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩) (P : NativeDomainPresentationAt B sp z U.2.obj.domain) :
    presentedFormalSum (presentedProductList L U P) = presentedFormalSum L * P.expression.formalValue := by
  induction L with
  | nil => simp [presentedFormalSum, presentedProductList]
  | cons V L ih =>
    change V.2.expression.formalValue * P.expression.formalValue +
      presentedFormalSum (presentedProductList L U P) =
      (V.2.expression.formalValue + presentedFormalSum L) * P.expression.formalValue
    rw [ih, add_mul]

end DiamondIntegral.Section5
