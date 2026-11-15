import «section 5».NativeRelationTermPresentations

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


theorem presentedOldObjects_append {z : Fin p → M}
    (L R : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    presentedOldObjects (L ++ R) = presentedOldObjects L ++ presentedOldObjects R := List.map_append

theorem presentedFormalSum_append {z : Fin p → M}
    (L R : List (PresentedGradedRESObjectAt (hc := hc) B sp z)) :
    presentedFormalSum (L ++ R) = presentedFormalSum L + presentedFormalSum R := by
  simp only [presentedFormalSum, List.map_append, List.sum_append]

structure NativeRelationListPresentationAt (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (terms : List (RelationTerm hc ⟨B.real ∪ Set.range z, B.gamma⟩)) where
  certificates : List (RESRelationCertificate B p sp)
  valid : ∀ I ∈ certificates, I.2.2.Valid hc z
  left : List (PresentedGradedRESObjectAt (hc := hc) B sp z)
  right : List (PresentedGradedRESObjectAt (hc := hc) B sp z)
  left_old : presentedOldObjects left = relationLeftFamily hc _ terms
  right_old : presentedOldObjects right = relationRightFamily hc _ terms
  left_formal : presentedFormalSum left = (resCertificateLeftExpression certificates).2.formalValue
  right_formal : presentedFormalSum right = (resCertificateRightExpression certificates).2.formalValue

theorem native_relation_list_presentation_exists (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (terms : List (RelationTerm hc ⟨B.real ∪ Set.range z, B.gamma⟩)) :
    Nonempty (NativeRelationListPresentationAt B sp z terms) := by
  induction terms with
  | nil => exact ⟨⟨[], (by simp), [], [], rfl, rfl, rfl, rfl⟩⟩
  | cons t terms ih =>
    obtain ⟨P⟩ := native_relation_term_presentation_exists B sp z hz t
    obtain ⟨Q⟩ := ih
    refine ⟨{
      certificates := P.certificate :: Q.certificates
      valid := ?_
      left := P.left ++ Q.left
      right := P.right ++ Q.right
      left_old := ?_
      right_old := ?_
      left_formal := ?_
      right_formal := ?_ }⟩
    · intro I hI
      rcases List.mem_cons.mp hI with rfl | hI
      · exact P.valid
      · exact Q.valid I hI
    · rw [presentedOldObjects_append, P.left_old, Q.left_old]
      rfl
    · rw [presentedOldObjects_append, P.right_old, Q.right_old]
      rfl
    · rw [presentedFormalSum_append, P.left_formal, Q.left_formal]
      rfl
    · rw [presentedFormalSum_append, P.right_formal, Q.right_formal]
      rfl

end DiamondIntegral.Section5
