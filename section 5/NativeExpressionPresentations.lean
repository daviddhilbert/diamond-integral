import «section 5».NativeSchemaPresentations
import «section 5».NativeProductBijections
import «section 5».RESExpressionSchemata

/-! Actual native objects have original-base finite expression
presentations. Empty objects, coproducts and products preserve actual
Gamma-ground domain bijections at the displayed parameter. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k l : ℕ} {sp : Fin p → SortTag}

structure NativeRESExpressionPresentationAt (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (U : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k) where
  arity : ℕ
  expression : RESExpressionSchema B p sp arity
  valid : expression.Valid hc z
  bijection : GammaGroundBijection
    (expression.setSchema.object hc z (expression.setSchema_valid hc z valid)).obj.domain U.obj.domain

theorem native_expression_presentation_exists (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (U : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k) :
    Nonempty (NativeRESExpressionPresentationAt B sp z U) := by
  obtain ⟨F, hF, _, ⟨f⟩⟩ := native_res_schema_at_parameter B sp z hz U
  exact ⟨⟨U.obj.arity, .atom F, hF, f⟩⟩

def NativeRESExpressionPresentationAt.empty (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (k : ℕ) :
    NativeRESExpressionPresentationAt B sp z (GammaGroundRESObject.empty hc ⟨B.real ∪ Set.range z, B.gamma⟩ k) where
  arity := 0
  expression := .empty
  valid := hz
  bijection := gammaGroundBijectionOfCarrierEq _ _ rfl

def NativeRESExpressionPresentationAt.coprod (z : Fin p → M)
    {U V : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k}
    (P : NativeRESExpressionPresentationAt B sp z U) (Q : NativeRESExpressionPresentationAt B sp z V) :
    NativeRESExpressionPresentationAt B sp z (U.coprod V) where
  arity := 1+(P.arity+Q.arity)
  expression := .sum P.expression Q.expression
  valid := ⟨P.valid, Q.valid⟩
  bijection := (gammaGroundRVTaggedUnionBijection P.bijection Q.bijection).comp
    (nativeSchemaSumBijection P.expression.setSchema Q.expression.setSchema z
      (P.expression.setSchema_valid hc z P.valid) (Q.expression.setSchema_valid hc z Q.valid))

def NativeRESExpressionPresentationAt.product (z : Fin p → M)
    {U : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ k}
    {V : GammaGroundRESObject hc ⟨B.real ∪ Set.range z, B.gamma⟩ l}
    (P : NativeRESExpressionPresentationAt B sp z U) (Q : NativeRESExpressionPresentationAt B sp z V) :
    NativeRESExpressionPresentationAt B sp z (U.product V) where
  arity := Q.arity+P.arity
  expression := .product P.expression Q.expression
  valid := ⟨P.valid, Q.valid⟩
  bijection := (nativeRawProductBijection P.bijection Q.bijection).comp
    (nativeSchemaProductBijection P.expression.setSchema Q.expression.setSchema z
      (P.expression.setSchema_valid hc z P.valid) (Q.expression.setSchema_valid hc z Q.valid))

end DiamondIntegral.Section5
