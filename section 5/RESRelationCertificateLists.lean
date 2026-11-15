import «section 5».RESExpressionRelations
import «section 5».RESStabilizationExpressions

/-! A finite relation list retains its actual native certificate trees,
with no equality of positive classes accepted as input. -/
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
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

abbrev RESRelationCertificate (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) :=
  (a : ℕ) × (b : ℕ) × RESExpressionRelationSchema B p sp a b

def resCertificateLeftExpression (L : List (RESRelationCertificate B p sp)) :
    (a : ℕ) × RESExpressionSchema B p sp a :=
  resExpressionListSum (L.map (fun I => ⟨I.1, I.2.2.leftExpression⟩))
def resCertificateRightExpression (L : List (RESRelationCertificate B p sp)) :
    (a : ℕ) × RESExpressionSchema B p sp a :=
  resExpressionListSum (L.map (fun I => ⟨I.2.1, I.2.2.rightExpression⟩))

theorem resCertificateLeftExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESRelationCertificate B p sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ I ∈ L, I.2.2.Valid hc z) :
    (resCertificateLeftExpression L).2.Valid hc z := by
  apply resExpressionListSum_valid hc _ z hz
  intro E hE
  obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hE
  exact (I.2.2.expressions_valid hc z (hL I hI)).1

theorem resCertificateRightExpression_valid (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESRelationCertificate B p sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ I ∈ L, I.2.2.Valid hc z) :
    (resCertificateRightExpression L).2.Valid hc z := by
  apply resExpressionListSum_valid hc _ z hz
  intro E hE
  obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hE
  exact (I.2.2.expressions_valid hc z (hL I hI)).2

theorem resCertificateExpressions_native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (L : List (RESRelationCertificate B p sp)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hL : ∀ I ∈ L, I.2.2.Valid hc z) :
    (resCertificateLeftExpression L).2.nativeValue hc z (resCertificateLeftExpression_valid hc L z hz hL) =
    (resCertificateRightExpression L).2.nativeValue hc z (resCertificateRightExpression_valid hc L z hz hL) := by
  induction L with
  | nil => rfl
  | cons I L ih =>
    exact congrArg₂ (fun x y => x+y) (I.2.2.native_equality hc z (hL I List.mem_cons_self))
      (ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)))

end DiamondIntegral.Section5
