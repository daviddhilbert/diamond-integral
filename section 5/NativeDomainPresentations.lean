import «section 5».NativeProductBijections
import «section 5».RESExpressionSchemata

/-! Finite expressions present arbitrary native finite-value RV domains.
Their target can be a literal tagged family with varying old degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n m : ℕ} {sp : Fin p → SortTag}

structure NativeDomainPresentationAt (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    {n : ℕ} (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawRVSpace (M := M) n)) where
  arity : ℕ
  expression : RESExpressionSchema B p sp arity
  valid : expression.Valid hc z
  bijection : GammaGroundBijection
    (expression.setSchema.object hc z (expression.setSchema_valid hc z valid)).obj.domain A

def NativeDomainPresentationAt.empty (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) :
    NativeDomainPresentationAt B sp z
      (GammaGroundDefSet.empty hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawRVSpace 0)) where
  arity := 0
  expression := .empty
  valid := hz
  bijection := gammaGroundBijectionOfCarrierEq _ _ rfl

def NativeDomainPresentationAt.sum (z : Fin p → M)
    {A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawRVSpace (M := M) n)}
    {C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawRVSpace (M := M) m)}
    (P : NativeDomainPresentationAt B sp z A) (Q : NativeDomainPresentationAt B sp z C) :
    NativeDomainPresentationAt B sp z (gammaGroundRVTaggedUnion A C) where
  arity := 1+(P.arity+Q.arity)
  expression := .sum P.expression Q.expression
  valid := ⟨P.valid, Q.valid⟩
  bijection := (gammaGroundRVTaggedUnionBijection P.bijection Q.bijection).comp
    (nativeSchemaSumBijection P.expression.setSchema Q.expression.setSchema z
      (P.expression.setSchema_valid hc z P.valid) (Q.expression.setSchema_valid hc z Q.valid))

def NativeDomainPresentationAt.product (z : Fin p → M)
    {A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawRVSpace (M := M) n)}
    {C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z, B.gamma⟩ (rawRVSpace (M := M) m)}
    (P : NativeDomainPresentationAt B sp z A) (Q : NativeDomainPresentationAt B sp z C) :
    NativeDomainPresentationAt B sp z (gammaGroundRVProductDomain A C) where
  arity := Q.arity+P.arity
  expression := .product P.expression Q.expression
  valid := ⟨P.valid, Q.valid⟩
  bijection := (nativeRawProductBijection P.bijection Q.bijection).comp
    (nativeSchemaProductBijection P.expression.setSchema Q.expression.setSchema z
      (P.expression.setSchema_valid hc z P.valid) (Q.expression.setSchema_valid hc z Q.valid))

def NativeDomainPresentationAt.taggedFinFamily (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) :
    (N : ℕ) → (A : Fin N → GammaRVSet hc ⟨B.real ∪ Set.range z, B.gamma⟩) →
    (∀ i, NativeDomainPresentationAt B sp z (A i).2) →
    NativeDomainPresentationAt B sp z (taggedRVFinFamily hc _ N A).2
  | 0, _, _ => NativeDomainPresentationAt.empty B sp z hz
  | N+1, A, P => (P 0).sum z
      (NativeDomainPresentationAt.taggedFinFamily B sp z hz N (fun i => A i.succ) (fun i => P i.succ))

end DiamondIntegral.Section5
