import «section 5».RESWholeCertificateSums
import «section 5».OriginalRVRowBijections
import «section 5».OriginalTaggedRowPresentations
import «section 5».RESFixedBijectionPromotion

/-! Actual whole-expression identity and coproduct graphs allow a finite
native equality witness to retain the positive contribution expressions
literally, rather than replacing them by new atomic objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b c d : ℕ} {sp : Fin p → SortTag}

def originalWholeCertificates (L : List (RESRelationCertificate B p sp)) :
    List (RESWholeRelationCertificate B p sp) := L.map (fun I => .original I.2.2)

theorem originalWholeCertificates_left (L : List (RESRelationCertificate B p sp)) :
    resWholeLeftPolynomial (originalWholeCertificates L) = (resCertificateLeftExpression L).2.formalValue := by
  induction L with
  | nil => rfl
  | cons I L ih =>
    change I.2.2.leftExpression.formalValue + resWholeLeftPolynomial (originalWholeCertificates L) =
      I.2.2.leftExpression.formalValue + (resCertificateLeftExpression L).2.formalValue
    rw [ih]

theorem originalWholeCertificates_right (L : List (RESRelationCertificate B p sp)) :
    resWholeRightPolynomial (originalWholeCertificates L) = (resCertificateRightExpression L).2.formalValue := by
  induction L with
  | nil => rfl
  | cons I L ih =>
    change I.2.2.rightExpression.formalValue + resWholeRightPolynomial (originalWholeCertificates L) =
      I.2.2.rightExpression.formalValue + (resCertificateRightExpression L).2.formalValue
    rw [ih]

theorem originalWholeCertificates_valid (L : List (RESRelationCertificate B p sp))
    (z : Fin p → M) (hv : ∀ I ∈ L, I.2.2.Valid hc z) :
    ∀ C ∈ originalWholeCertificates L, C.Valid hc z := by
  intro C hC
  obtain ⟨I,hI,rfl⟩ := List.mem_map.mp hC
  exact hv I hI

theorem resExpression_atom_bijections_at_parameter
    (E : RESExpressionSchema B p sp a) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hv : E.Valid hc z) :
    ∃ H : RESExpressionBijectionSchema E (.atom E.setSchema),
      ∃ K : RESExpressionBijectionSchema (.atom E.setSchema) E, H.Valid hc z ∧ K.Valid hc z := by
  obtain ⟨H,hH⟩ := res_expression_bijection_schema_at_parameter B sp z hz E (.atom E.setSchema)
    hv (E.setSchema_valid hc z hv) (GammaGroundBijection.id _)
  obtain ⟨K,hK⟩ := res_expression_bijection_schema_at_parameter B sp z hz (.atom E.setSchema) E
    (E.setSchema_valid hc z hv) hv (GammaGroundBijection.id _)
  exact ⟨H,K,hH,hK⟩

def originalRVExpressionSumBijection
    (E : RESExpressionSchema B p sp a) (F : RESExpressionSchema B p sp b)
    (G : RESExpressionSchema B p sp c) (H : RESExpressionSchema B p sp d) (z : Fin p → M)
    (f : GammaGroundBijection (originalRVRowDomain hc E.setSchema.domain z)
      (originalRVRowDomain hc G.setSchema.domain z))
    (g : GammaGroundBijection (originalRVRowDomain hc F.setSchema.domain z)
      (originalRVRowDomain hc H.setSchema.domain z)) :
    GammaGroundBijection (originalRVRowDomain hc (E.sum F).setSchema.domain z)
      (originalRVRowDomain hc (G.sum H).setSchema.domain z) :=
  (originalRVRowTaggedBijection G.setSchema.domain H.setSchema.domain z).symm.comp
    ((gammaGroundRVTaggedUnionBijection f g).comp
      (originalRVRowTaggedBijection E.setSchema.domain F.setSchema.domain z))

end DiamondIntegral.Section5
