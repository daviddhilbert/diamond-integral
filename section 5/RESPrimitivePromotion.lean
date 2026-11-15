import «section 5».NativeSchemaPresentations
import «section 5».RESExpressionRelations
import «section 5».RESBijectionPromotion
import «section 5».GammaConstantValueSchemata
import «section 5».RESLiteralRelationTerms

/-! Every old literal native primitive over a displayed parameter has an
original-base finite certificate and actual endpoint-domain bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

structure RESPrimitivePresentationAt (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (P : RESFiniteWitness.PrimitivePair hc ⟨B.real ∪ Set.range z, B.gamma⟩) where
  leftArity : ℕ
  rightArity : ℕ
  schema : RESExpressionRelationSchema B p sp leftArity rightArity
  valid : schema.Valid hc z
  left : GammaGroundBijection
    (schema.leftExpression.setSchema.object hc z
      (schema.leftExpression.setSchema_valid hc z (schema.expressions_valid hc z valid).1)).obj.domain
    P.leftObject.2.obj.domain
  right : GammaGroundBijection
    (schema.rightExpression.setSchema.object hc z
      (schema.rightExpression.setSchema_valid hc z (schema.expressions_valid hc z valid).2)).obj.domain
    P.rightObject.2.obj.domain

theorem res_primitive_schema_at_parameter (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (P : RESFiniteWitness.PrimitivePair hc ⟨B.real ∪ Set.range z, B.gamma⟩) :
    Nonempty (RESPrimitivePresentationAt B sp z P) := by
  cases P with
  | underlying A C f =>
    obtain ⟨F, G, H, hv, hF, hG, _⟩ := res_bijection_schema_at_parameter hc B sp z hz A C f
    let U := Section3RVChartBridge.nativeRES hc A
    let V := Section3RVChartBridge.nativeRES hc C
    have hrowF : F.rowDomain z = rawDomain U.obj.domain :=
      hF.trans (rawDomain_ofRaw A.domain A.domain_definable).symm
    have hrowG : G.rowDomain z = rawDomain V.obj.domain :=
      hG.trans (rawDomain_ofRaw C.domain C.domain_definable).symm
    exact ⟨{
      leftArity := A.arity
      rightArity := C.arity
      schema := .underlying F G H
      valid := hv
      left := nativeSchemaPresentation z U F hv.1 hrowF
      right := nativeSchemaPresentation z V G hv.2.1 hrowG }⟩
  | fibre α hα =>
    obtain ⟨F, hF, hval⟩ := gamma_value_schema_at_parameter hc B sp z hz α hα
    let O : GammaValueSchema B p sp := GammaValueSchema.constant 1 (GammaGroupNames.one_definable_base B)
    have hO := GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) z hz
    let A := RESFibreObjects.fibre ⟨B.real ∪ Set.range z, B.gamma⟩ α 1 hα (GammaGroupNames.one_definable_base _)
    let C := RESFibreObjects.torus ⟨B.real ∪ Set.range z, B.gamma⟩
    let U := Section3RVChartBridge.nativeRES hc A
    let V := Section3RVChartBridge.nativeRES hc C
    have hrowF : F.resSchema.rowDomain z = rawDomain U.obj.domain := by
      rw [show rawDomain U.obj.domain = A.domain from rawDomain_ofRaw A.domain A.domain_definable]
      ext x
      change Fin.append z x ∈ F.domain.val ↔ Proper x ∧ codeValue (x 0) = α
      rw [F.value_row hc z hF x, hval]
    have hrowO : O.resSchema.rowDomain z = rawDomain V.obj.domain := by
      rw [show rawDomain V.obj.domain = C.domain from rawDomain_ofRaw C.domain C.domain_definable]
      ext x
      change Fin.append z x ∈ O.domain.val ↔ Proper x ∧ codeValue (x 0) = 1
      exact GammaValueSchema.constant_row 1 (GammaGroupNames.one_definable_base B) z hz x
    exact ⟨{
      leftArity := 1
      rightArity := 1
      schema := .fibre F O
      valid := ⟨hF, hO⟩
      left := nativeSchemaPresentation z U F.resSchema hF.1 hrowF
      right := nativeSchemaPresentation z V O.resSchema hO.1 hrowO }⟩

end DiamondIntegral.Section5
