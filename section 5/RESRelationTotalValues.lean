import «section 5».RESRelativeFormalEvaluation
import «section 5».GammaValueCoefficientTotals
import «section 5».RESExpressionRelations
import «section 5».RESBijectionRealization
import «section 5».RESRelationCertificateLists

/-! Every original primitive RES relation, with arbitrary shared-base
coefficient expressions and orientation, preserves actual total native
values. Underlying graphs and varying value torsors are proved separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

def RESBijectionSchema.actualRowBijection
    {F : RESSetSchema B p a (fun _ => .rv)} {G : RESSetSchema B p b (fun _ => .rv)}
    (H : RESBijectionSchema F G) (z : Fin p → M) (h : H.Valid hc z) :
    GammaGroundBijection (originalRVRowDomain hc F.domain z) (originalRVRowDomain hc G.domain z) :=
  rawEquivalenceBijection (F.rowDomain z) (G.rowDomain z) (F.row_domain_definable z) (G.row_domain_definable z)
    (H.rawEquiv hc z h) (H.raw_joined_graph_definable hc z h)

theorem relativeRESFormalEvaluator_atom
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RESSetSchema B p a (fun _ => .rv)) :
    relativeRESFormalEvaluator X (FreeCommRing.of ⟨a,F⟩) = relativeRVFamilyClass X ⟨a,F.domain⟩ :=
  FreeCommRing.lift_of (fun A : RESAtomSchema B p (fun _ => .rv) =>
    relativeRVFamilyClass X ⟨A.1,A.2.domain⟩) ⟨a,F⟩

theorem RESExpressionRelationSchema.total_coefficient_equality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (R : RESExpressionRelationSchema B p (fun _ => .rv) a b)
    (hv : ∀ x : X, R.Valid hc (rvValues x.val)) (D : RelativeRVFamily B p) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRESFormalEvaluator X R.leftExpression.formalValue) =
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRESFormalEvaluator X R.rightExpression.formalValue) := by
  induction R generalizing D with
  | underlying F G H =>
    have he : relativeRVFamilyClass X ⟨_,F.domain⟩ = relativeRVFamilyClass X ⟨_,G.domain⟩ :=
      relativeRVCompletedClass_iso X (fun x => ⟨H.actualRowBijection _ (hv x)⟩)
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRESFormalEvaluator X (FreeCommRing.of ⟨_,F⟩)) =
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRVFamilyClass X D * relativeRESFormalEvaluator X (FreeCommRing.of ⟨_,G⟩))
    rw [relativeRESFormalEvaluator_atom,relativeRESFormalEvaluator_atom,he]
  | fibre F G =>
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRESFormalEvaluator X (FreeCommRing.of ⟨1,F.resSchema⟩)) =
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRVFamilyClass X D * relativeRESFormalEvaluator X (FreeCommRing.of ⟨1,G.resSchema⟩))
    rw [relativeRESFormalEvaluator_atom,relativeRESFormalEvaluator_atom]
    exact (nativeRelativeRVForget_value_product h00 linear hκ hs hr hγ hΓ kind X D F (fun x => (hv x).1)).trans
      (nativeRelativeRVForget_value_product h00 linear hκ hs hr hγ hΓ kind X D G (fun x => (hv x).2)).symm
  | reverse R ih => exact (ih hv D).symm
  | @multiplyLeft a b c C R ih =>
    let E : RelativeRVFamily B p := ⟨c,C.setSchema.domain⟩
    have he := C.relative_formal_evaluate X (fun x => (hv x).1)
    have h := ih (fun x => (hv x).2) (D.blockProduct E)
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRESFormalEvaluator X (C.formalValue * R.leftExpression.formalValue)) =
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRVFamilyClass X D * relativeRESFormalEvaluator X (C.formalValue * R.rightExpression.formalValue))
    rw [(relativeRESFormalEvaluator X).map_mul,(relativeRESFormalEvaluator X).map_mul,he]
    simpa only [relativeRVCompletedClass_product,mul_assoc] using h

theorem RESExpressionRelationSchema.total_formal_equality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (R : RESExpressionRelationSchema B p (fun _ => .rv) a b)
    (hv : ∀ x : X, R.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X R.leftExpression.formalValue) =
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X R.rightExpression.formalValue) := by
  have h := R.total_coefficient_equality h00 linear hκ hs hr hγ hΓ kind X hv (RelativeRVFamily.one B p)
  have he : relativeRVFamilyClass X (RelativeRVFamily.one B p) = 1 := rfl
  simpa only [he,one_mul] using h

theorem resCertificateExpressions_total_formal_equality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (L : List (RESRelationCertificate B p (fun _ => .rv)))
    (hv : ∀ x : X, ∀ I ∈ L, I.2.2.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (resCertificateLeftExpression L).2.formalValue) =
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (resCertificateRightExpression L).2.formalValue) := by
  induction L with
  | nil => rfl
  | cons I L ih =>
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X
        (I.2.2.leftExpression.formalValue + (resCertificateLeftExpression L).2.formalValue)) =
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRESFormalEvaluator X
          (I.2.2.rightExpression.formalValue + (resCertificateRightExpression L).2.formalValue))
    simp only [map_add]
    exact congrArg₂ (fun u v => u+v)
      (I.2.2.total_formal_equality h00 linear hκ hs hr hγ hΓ kind X
        (fun x => hv x I List.mem_cons_self))
      (ih (fun x J hJ => hv x J (List.mem_cons_of_mem _ hJ)))

end DiamondIntegral.Section5
