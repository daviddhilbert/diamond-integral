import «section 5».RVEvaluationEqualitySchemata
import «section 5».RESExpressionSplicing
import «section 5».RESLayoutUniformity
import «section 5».RVRectangleDecompositionExistence

/-! Actual equality of native RV rows supplies an entire original-base
finite equality package, including both rectangles and its full graph.
The positive contribution expressions are retained by actual splicing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
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
variable {p a b : ℕ} {sp : Fin p → SortTag}

theorem rv_evaluation_equality_schema_at_parameter
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (he : nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E z) :
    ∃ W : RVEvaluationEqualitySchema hc kind D E, W.Valid hc z := by
  obtain ⟨U,hU⟩ := rv_rectangle_decomposition_schema_at_parameter hc h00 hκ hs hr hγ hΓ D z hz
  obtain ⟨V,hV⟩ := rv_rectangle_decomposition_schema_at_parameter hc h00 hκ hs hr hγ hΓ E z hz
  let P := (U.positiveExpression hc kind).2.sum (V.negativeExpression hc kind).2
  let Q := (U.negativeExpression hc kind).2.sum (V.positiveExpression hc kind).2
  have hP : P.Valid hc z := ⟨U.positiveExpression_valid kind z hU,V.negativeExpression_valid kind z hV⟩
  have hQ : Q.Valid hc z := ⟨U.negativeExpression_valid kind z hU,V.positiveExpression_valid kind z hV⟩
  have hPQ : nativeRESChartClass (P.setSchema.chart hc z (P.setSchema_valid hc z hP)) =
      nativeRESChartClass (Q.setSchema.chart hc z (Q.setSchema_valid hc z hQ)) := by
    rw [P.nativeClass_eq hc z hP,Q.nativeClass_eq hc z hQ]
    have hr := (U.positive_negative_row_value h00 linear hκ hs hr hγ hΓ kind z hU).trans
      (he.trans (V.positive_negative_row_value h00 linear hκ hs hr hγ hΓ kind z hV).symm)
    exact (sub_eq_sub_iff_add_eq_add.mp hr).trans (add_comm _ _)
  obtain ⟨H,hH⟩ := res_layout_schema_exists_of_native_equality B sp z hz P.setSchema Q.setSchema
    (P.setSchema_valid hc z hP) (Q.setSchema_valid hc z hQ) hPQ
  obtain ⟨hrootP,hrootQ,hstab,hrels,hsource,htarget,hbij⟩ := hH
  obtain ⟨HP,_,hHP,_⟩ := resExpression_atom_bijections_at_parameter P z hz hP
  obtain ⟨_,HQ,_,hHQ⟩ := resExpression_atom_bijections_at_parameter Q z hz hQ
  let L : List (RESWholeRelationCertificate B p sp) := originalWholeCertificates H.relations ++
    [.whole P (.atom P.setSchema) HP,.whole (.atom Q.setSchema) Q HQ]
  have hL : ∀ C ∈ L, C.Valid hc z := by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact originalWholeCertificates_valid H.relations z hrels C hC
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
      rcases hC with rfl | rfl
      · exact hHP
      · exact hHQ
  have hLeft : resWholeLeftPolynomial L = (resCertificateLeftExpression H.relations).2.formalValue +
      (P.formalValue + FreeCommRing.of ⟨_,Q.setSchema⟩) := by
    change ((L.map (fun C => C.leftExpression.2.formalValue)).sum) = _
    dsimp only [L]
    rw [List.map_append,List.sum_append]
    change resWholeLeftPolynomial (originalWholeCertificates H.relations) +
      (P.formalValue + (FreeCommRing.of ⟨_,Q.setSchema⟩+0)) = _
    rw [originalWholeCertificates_left,add_zero]
  have hRight : resWholeRightPolynomial L = (resCertificateRightExpression H.relations).2.formalValue +
      (FreeCommRing.of ⟨_,P.setSchema⟩ + Q.formalValue) := by
    change ((L.map (fun C => C.rightExpression.2.formalValue)).sum) = _
    dsimp only [L]
    rw [List.map_append,List.sum_append]
    change resWholeRightPolynomial (originalWholeCertificates H.relations) +
      (FreeCommRing.of ⟨_,P.setSchema⟩ + (Q.formalValue+0)) = _
    rw [originalWholeCertificates_right,add_zero]
  let S := H.source.sum (P.sum Q)
  let T := H.target.sum (P.sum Q)
  have hs : S.Valid hc z := ⟨hsource,hP,hQ⟩
  have ht : T.Valid hc z := ⟨htarget,hP,hQ⟩
  let f := originalRVExpressionSumBijection H.source (P.sum Q) H.target (P.sum Q) z
    (originalRVRowBijection (hc := hc) H.source.setSchema.domain H.target.setSchema.domain H.graph z hbij)
    (GammaGroundBijection.id _)
  obtain ⟨G,hG⟩ := original_fixed_rv_bijection_schema_at_parameter hc B sp z hz
    S.setSchema.domain T.setSchema.domain (originalRVRowDomain hc S.setSchema.domain z)
    (originalRVRowDomain hc T.setSchema.domain z)
    (originalRVRowDomain_raw S.setSchema.domain z).symm (originalRVRowDomain_raw T.setSchema.domain z).symm f
  let torus : GammaValueSchema B p sp := GammaValueSchema.constant 1 (GammaGroupNames.one_definable_base B)
  have hpformal : P.formalValue = U.positivePolynomial hc kind torus.resSchema +
      V.negativePolynomial hc kind torus.resSchema := by
    change (U.positiveExpression hc kind).2.formalValue + (V.negativeExpression hc kind).2.formalValue = _
    rw [U.positiveExpression_formal,V.negativeExpression_formal]
    rfl
  have hqformal : Q.formalValue = U.negativePolynomial hc kind torus.resSchema +
      V.positivePolynomial hc kind torus.resSchema := by
    change (U.negativeExpression hc kind).2.formalValue + (V.positiveExpression hc kind).2.formalValue = _
    rw [U.negativeExpression_formal,V.positiveExpression_formal]
    rfl
  let W : RVEvaluationEqualitySchema hc kind D E := {
    leftRectangles := U
    rightRectangles := V
    torus := torus
    stabilizerArity := H.stabilizerArity
    stabilizer := H.stabilizer
    relations := L
    sourceArity := _
    targetArity := _
    source := S
    target := T
    source_formal := by
      change H.source.formalValue + (P.formalValue+Q.formalValue) = _
      rw [H.source_formal,hRight,←hpformal]
      abel
    target_formal := by
      change H.target.formalValue + (P.formalValue+Q.formalValue) = _
      rw [H.target_formal,hLeft,←hqformal]
      abel
    graph := G }
  exact ⟨W,hU,hV,GammaValueSchema.constant_valid hc 1 (GammaGroupNames.one_definable_base B) z hz,
    hstab,hs,ht,⟨hz,hL⟩,hG⟩

end DiamondIntegral.Section5
