import «section 5».RESRelationCertificateLists
import «section 5».RESExpressionRelationRecoding
import «section 5».RESFormalRecoding

/-! Finite certificate lists and their formal values retain the same
numerical arities and polynomial identities under literal row recoding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def recodeRESCertificate (R : GammaParameterRecode B p q sp sq) (I : RESRelationCertificate B p sp) :
    RESRelationCertificate B q sq := ⟨I.1, I.2.1, I.2.2.recode R⟩

theorem resExpressionListSum_formal (L : List ((a : ℕ) × RESExpressionSchema B p sp a)) :
    (resExpressionListSum L).2.formalValue = (L.map (fun E => E.2.formalValue)).sum := by
  induction L with
  | nil => rfl
  | cons E L ih =>
    change E.2.formalValue + (resExpressionListSum L).2.formalValue = _
    rw [ih]
    rfl

theorem resCertificateLeft_formal_recode (R : GammaParameterRecode B p q sp sq)
    (L : List (RESRelationCertificate B p sp)) :
    (resCertificateLeftExpression (L.map (recodeRESCertificate R))).2.formalValue =
      formalSchemaRecode R (resCertificateLeftExpression L).2.formalValue := by
  induction L with
  | nil => exact (map_zero _).symm
  | cons I L ih =>
    change (I.2.2.recode R).leftExpression.formalValue +
      (resCertificateLeftExpression (L.map (recodeRESCertificate R))).2.formalValue =
      formalSchemaRecode R (I.2.2.leftExpression.formalValue + (resCertificateLeftExpression L).2.formalValue)
    rw [(I.2.2.expressions_recode R).1, RESExpressionSchema.formalValue_recode, ih, map_add]

theorem resCertificateRight_formal_recode (R : GammaParameterRecode B p q sp sq)
    (L : List (RESRelationCertificate B p sp)) :
    (resCertificateRightExpression (L.map (recodeRESCertificate R))).2.formalValue =
      formalSchemaRecode R (resCertificateRightExpression L).2.formalValue := by
  induction L with
  | nil => exact (map_zero _).symm
  | cons I L ih =>
    change (I.2.2.recode R).rightExpression.formalValue +
      (resCertificateRightExpression (L.map (recodeRESCertificate R))).2.formalValue =
      formalSchemaRecode R (I.2.2.rightExpression.formalValue + (resCertificateRightExpression L).2.formalValue)
    rw [(I.2.2.expressions_recode R).2, RESExpressionSchema.formalValue_recode, ih, map_add]

end DiamondIntegral.Section5
