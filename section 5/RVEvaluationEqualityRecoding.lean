import «section 5».RVEvaluationEqualitySchemata

/-! Whole RV evaluation certificates retain their fixed numerical data,
formal contribution identities and actual full graph after row recoding. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag} {kind : EulerKind}

def RVEvaluationEqualitySchema.recode
    (R : GammaParameterRecode B p q sp sq)
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) :
    RVEvaluationEqualitySchema hc kind (R.domain D) (R.domain E) where
  leftRectangles := W.leftRectangles.recode R
  rightRectangles := W.rightRectangles.recode R
  torus := W.torus.recode R
  stabilizerArity := W.stabilizerArity
  stabilizer := W.stabilizer.recode R
  relations := W.relations.map (RESWholeRelationCertificate.recode R)
  sourceArity := W.sourceArity
  targetArity := W.targetArity
  source := W.source.recode R
  target := W.target.recode R
  source_formal := by
    rw [RESExpressionSchema.formalValue_recode,W.source_formal,map_add,map_add,map_add,
      ←W.leftRectangles.positivePolynomial_recode R hc kind W.torus.resSchema,
      ←W.rightRectangles.negativePolynomial_recode R hc kind W.torus.resSchema,
      ←W.stabilizer.formalValue_recode R,←resWholeRightPolynomial_recode R W.relations]
    rfl
  target_formal := by
    rw [RESExpressionSchema.formalValue_recode,W.target_formal,map_add,map_add,map_add,
      ←W.leftRectangles.negativePolynomial_recode R hc kind W.torus.resSchema,
      ←W.rightRectangles.positivePolynomial_recode R hc kind W.torus.resSchema,
      ←W.stabilizer.formalValue_recode R,←resWholeLeftPolynomial_recode R W.relations]
    rfl
  graph := R.relation W.graph

def RVEvaluationEqualitySchema.RowAgreement
    (R : GammaParameterRecode B p q sp sq)
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) (z : Fin p → M) (t : Fin q → M) : Prop :=
  R.DomainAgreement D z t ∧ R.DomainAgreement E z t ∧
    (∀ i, (W.leftRectangles.cells i).RowAgreement R z t) ∧
    (∀ i, (W.rightRectangles.cells i).RowAgreement R z t) ∧
    R.DomainAgreement W.torus.domain z t ∧ W.stabilizer.RowAgreement R z t ∧
    W.source.RowAgreement R z t ∧ W.target.RowAgreement R z t ∧
    (∀ C ∈ W.relations, C.RowAgreement R z t) ∧ R.RelationAgreement W.graph z t

theorem RVEvaluationEqualitySchema.recode_valid_iff
    (R : GammaParameterRecode B p q sp sq)
    {D : GammaDomainFormula B p a sp} {E : GammaDomainFormula B p b sp}
    (W : RVEvaluationEqualitySchema hc kind D E) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : W.RowAgreement R z t) : W.Valid hc z ↔ (W.recode R).Valid hc t := by
  obtain ⟨hD,hE,hL,hR,hT,hC,hS,hU,hI,hH⟩ := hrow
  have hl := W.leftRectangles.recode_valid_iff hc R z t hz ht hD hL
  have hr := W.rightRectangles.recode_valid_iff hc R z t hz ht hE hR
  have htorus := W.torus.recode_valid_iff hc R z t hz ht hT
  have hstab := W.stabilizer.recode_valid_iff hc R z t hz ht hC
  have hsource := W.source.recode_valid_iff hc R z t hz ht hS
  have htarget := W.target.recode_valid_iff hc R z t hz ht hU
  have hcert : (∀ C ∈ W.relations, C.Valid hc z) ↔
      ∀ C ∈ W.relations.map (RESWholeRelationCertificate.recode R), C.Valid hc t := by
    rw [List.forall_mem_map]
    exact forall_congr' (fun C => imp_congr_right (fun hC => C.recode_valid_iff hc R z t hz ht (hI C hC)))
  have hbij : bijectiveMapRowValid sp (fun _ : Fin W.targetArity => .rv)
      W.source.setSchema.domain.val W.target.setSchema.domain.val W.graph.val z ↔
      bijectiveMapRowValid sq (fun _ : Fin W.targetArity => .rv)
        (W.source.recode R).setSchema.domain.val (W.target.recode R).setSchema.domain.val
          (R.relation W.graph).val t := by
    constructor
    · exact bijectiveMapRowValid_of_rows ht (W.source.recode_row_iff R z t hS)
        (W.target.recode_row_iff R z t hU) hH
    · exact bijectiveMapRowValid_of_rows hz (fun x => (W.source.recode_row_iff R z t hS x).symm)
        (fun x => (W.target.recode_row_iff R z t hU x).symm) (fun x y => (hH x y).symm)
  exact and_congr hl (and_congr hr (and_congr htorus (and_congr hstab
    (and_congr hsource (and_congr htarget (and_congr (and_congr (iff_of_true hz ht) hcert) hbij))))))

end DiamondIntegral.Section5
