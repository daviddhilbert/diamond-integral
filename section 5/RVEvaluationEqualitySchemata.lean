import «section 5».RESWholeCertificateSums
import «section 5».NativeRectanglePolynomialValues

/-! A complete original-language equality package retains both rectangle
decompositions and an actual stabilized graph for their signed residue
contributions. Its genuine first-order validity proves native row equality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

structure RVEvaluationEqualitySchema (hc : CanonicalStructure.IsCanonical (M := M)) (kind : EulerKind)
    (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp) where
  leftRectangles : RVRectangleDecompositionSchema D
  rightRectangles : RVRectangleDecompositionSchema E
  torus : GammaValueSchema B p sp
  stabilizerArity : ℕ
  stabilizer : RESExpressionSchema B p sp stabilizerArity
  relations : List (RESWholeRelationCertificate B p sp)
  sourceArity : ℕ
  targetArity : ℕ
  source : RESExpressionSchema B p sp sourceArity
  target : RESExpressionSchema B p sp targetArity
  source_formal : source.formalValue =
    (leftRectangles.positivePolynomial hc kind torus.resSchema +
      rightRectangles.negativePolynomial hc kind torus.resSchema) +
        (stabilizer.formalValue + resWholeRightPolynomial relations)
  target_formal : target.formalValue =
    (leftRectangles.negativePolynomial hc kind torus.resSchema +
      rightRectangles.positivePolynomial hc kind torus.resSchema) +
        (stabilizer.formalValue + resWholeLeftPolynomial relations)
  graph : GammaRelationFormula B p sourceArity targetArity sp

def RVEvaluationEqualitySchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {kind : EulerKind} {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) (z : Fin p → M) : Prop :=
  W.leftRectangles.Valid hc z ∧ W.rightRectangles.Valid hc z ∧ W.torus.Valid hc z ∧
    W.stabilizer.Valid hc z ∧ W.source.Valid hc z ∧ W.target.Valid hc z ∧
      ((∀ i, sortEval (sp i) (z i)) ∧ ∀ C ∈ W.relations, C.Valid hc z) ∧
        bijectiveMapRowValid sp (fun _ : Fin W.targetArity => .rv)
          W.source.setSchema.domain.val W.target.setSchema.domain.val W.graph.val z

theorem RVEvaluationEqualitySchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {kind : EulerKind} {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) : DefinableOverBase B sp {z | W.Valid hc z} := by
  have hrel := original_list_predicate_validity_definable W.relations
    (fun C z => C.Valid hc z) (fun C _ => C.valid_definable hc)
  have hb := gamma_bijection_validity_definable sp (fun _ : Fin W.sourceArity => .rv)
    (fun _ : Fin W.targetArity => .rv)
    W.source.setSchema.domain.property W.target.setSchema.domain.property W.graph.property
  exact (W.leftRectangles.valid_definable hc).inter ((W.rightRectangles.valid_definable hc).inter
    ((W.torus.valid_definable hc).inter ((W.stabilizer.valid_definable hc).inter
      ((W.source.valid_definable hc).inter ((W.target.valid_definable hc).inter (hrel.inter hb))))))

theorem RVEvaluationEqualitySchema.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {kind : EulerKind}
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) (z : Fin p → M) (hv : W.Valid hc z) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind D z =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind E z := by
  obtain ⟨hl,hr',ht,hc',hs',ht',hrel,hbij⟩ := hv
  let H : RESExpressionBijectionSchema W.source W.target := ⟨W.graph⟩
  have hgraph := H.native_equality hc z ⟨hs',ht',hbij⟩
  let ev := nativeSchemaEvaluator (B := B) (sp := sp) hc z
  have he : ev W.source.formalValue = ev W.target.formalValue :=
    (W.source.formalValue_evaluate hc z hs').trans
      (hgraph.trans (W.target.formalValue_evaluate hc z ht').symm)
  have hsPoly := congrArg ev W.source_formal
  have htPoly := congrArg ev W.target_formal
  simp only [map_add] at hsPoly htPoly
  have hcancel := hsPoly.symm.trans (he.trans htPoly)
  have hrelations : ev (resWholeLeftPolynomial W.relations) = ev (resWholeRightPolynomial W.relations) :=
    resWholePolynomials_native_equality hc W.relations z hrel.2
  rw [hrelations] at hcancel
  have hsum := add_right_cancel hcancel
  have hdiff : ev (W.leftRectangles.positivePolynomial hc kind W.torus.resSchema) -
      ev (W.leftRectangles.negativePolynomial hc kind W.torus.resSchema) =
      ev (W.rightRectangles.positivePolynomial hc kind W.torus.resSchema) -
        ev (W.rightRectangles.negativePolynomial hc kind W.torus.resSchema) :=
    sub_eq_sub_iff_add_eq_add.mpr (hsum.trans (add_comm _ _))
  exact (W.leftRectangles.positive_negative_polynomial_row_value h00 linear hκ hs hr hγ hΓ kind
    W.torus z hl ht).symm.trans
      (hdiff.trans (W.rightRectangles.positive_negative_polynomial_row_value h00 linear hκ hs hr hγ hΓ kind
        W.torus z hr' ht))

end DiamondIntegral.Section5
