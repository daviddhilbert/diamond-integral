import «section 5».NativePresentedLists
import «section 5».RESPrimitivePromotion

/-! Literal ideal terms retain their coefficient occurrences, orientation,
old native domains and original-base formal relation certificate. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

structure NativeRelationFamiliesPresentationAt (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (L R : List (GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩)) where
  certificate : RESRelationCertificate B p sp
  valid : certificate.2.2.Valid hc z
  left : List (PresentedGradedRESObjectAt (hc := hc) B sp z)
  right : List (PresentedGradedRESObjectAt (hc := hc) B sp z)
  left_old : presentedOldObjects left = L
  right_old : presentedOldObjects right = R
  left_formal : presentedFormalSum left = certificate.2.2.leftExpression.formalValue
  right_formal : presentedFormalSum right = certificate.2.2.rightExpression.formalValue

def native_coefficient_relation_presentation (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (C : List (PresentedGradedRESObjectAt (hc := hc) B sp z))
    (U V : GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩)
    (R : RESExpressionRelationSchema B p sp a b) (hR : R.Valid hc z)
    (f : GammaGroundBijection (R.leftExpression.setSchema.object hc z
      (R.leftExpression.setSchema_valid hc z (R.expressions_valid hc z hR).1)).obj.domain U.2.obj.domain)
    (g : GammaGroundBijection (R.rightExpression.setSchema.object hc z
      (R.rightExpression.setSchema_valid hc z (R.expressions_valid hc z hR).2)).obj.domain V.2.obj.domain) :
    NativeRelationFamiliesPresentationAt B sp z
      (positiveFamilyProduct hc _ (presentedOldObjects C) [U])
      (positiveFamilyProduct hc _ (presentedOldObjects C) [V]) := by
  let P : NativeDomainPresentationAt B sp z U.2.obj.domain :=
    ⟨a, R.leftExpression, (R.expressions_valid hc z hR).1, f⟩
  let Q : NativeDomainPresentationAt B sp z V.2.obj.domain :=
    ⟨b, R.rightExpression, (R.expressions_valid hc z hR).2, g⟩
  let E := presentedCoefficientExpression C
  refine {
    certificate := ⟨a+E.1, b+E.1, .multiplyLeft E.2 R⟩
    valid := ⟨presentedCoefficientExpression_valid C hz, hR⟩
    left := presentedProductList C U P
    right := presentedProductList C V Q
    left_old := presentedProductList_old C U P
    right_old := presentedProductList_old C V Q
    left_formal := ?_
    right_formal := ?_ }
  · change presentedFormalSum (presentedProductList C U P) = E.2.formalValue * R.leftExpression.formalValue
    rw [presentedProductList_formal]
    exact congrArg (fun x => x * R.leftExpression.formalValue) (presentedCoefficientExpression_formal C).symm
  · change presentedFormalSum (presentedProductList C V Q) = E.2.formalValue * R.rightExpression.formalValue
    rw [presentedProductList_formal]
    exact congrArg (fun x => x * R.rightExpression.formalValue) (presentedCoefficientExpression_formal C).symm

theorem native_relation_term_presentation_exists (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (t : RelationTerm hc ⟨B.real ∪ Set.range z, B.gamma⟩) :
    Nonempty (NativeRelationFamiliesPresentationAt B sp z t.leftFamily t.rightFamily) := by
  rcases t with ⟨primitive, coefficient, reversed⟩
  obtain ⟨P⟩ := res_primitive_schema_at_parameter B sp z hz primitive
  obtain ⟨C, hC⟩ := native_presented_list_exists B sp z hz coefficient
  cases reversed with
  | false =>
    have H := native_coefficient_relation_presentation z hz C primitive.leftObject primitive.rightObject
      P.schema P.valid P.left P.right
    simpa only [RelationTerm.leftFamily, RelationTerm.rightFamily, Bool.false_eq_true, if_false, hC] using
      (Nonempty.intro H)
  | true =>
    have H := native_coefficient_relation_presentation z hz C primitive.rightObject primitive.leftObject
      (.reverse P.schema) P.valid P.right P.left
    simpa only [RelationTerm.leftFamily, RelationTerm.rightFamily, if_true, hC] using (Nonempty.intro H)

end DiamondIntegral.Section5
