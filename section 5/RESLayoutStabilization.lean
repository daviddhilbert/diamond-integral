import «section 5».RESRelationCertificateLists
import «section 5».RESFormalExpressions
import «section 5».RESStabilizationSchemata

/-! A whole equality witness may retain its original finite domain layout.
Purely formal polynomial identities certify the layout; the only geometric
comparison input is its full actual total-domain bijection graph. -/
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

structure RESLayoutStabilizationSchema (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) where
  stabilizerArity : ℕ
  stabilizer : RESExpressionSchema B p sp stabilizerArity
  relations : List (RESRelationCertificate B p sp)
  sourceArity : ℕ
  targetArity : ℕ
  source : RESExpressionSchema B p sp sourceArity
  target : RESExpressionSchema B p sp targetArity
  source_formal : source.formalValue = FreeCommRing.of ⟨a, F⟩ +
    (stabilizer.formalValue + (resCertificateRightExpression relations).2.formalValue)
  target_formal : target.formalValue = FreeCommRing.of ⟨b, G⟩ +
    (stabilizer.formalValue + (resCertificateLeftExpression relations).2.formalValue)
  graph : GammaRelationFormula B p sourceArity targetArity sp

def RESLayoutStabilizationSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) (z : Fin p → M) : Prop :=
  F.Valid hc z ∧ G.Valid hc z ∧ W.stabilizer.Valid hc z ∧
    (∀ I ∈ W.relations, I.2.2.Valid hc z) ∧ W.source.Valid hc z ∧ W.target.Valid hc z ∧
    bijectiveMapRowValid sp (fun _ : Fin W.targetArity => .rv)
      W.source.setSchema.domain.val W.target.setSchema.domain.val W.graph.val z

theorem RESLayoutStabilizationSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) : DefinableOverBase B sp {z | W.Valid hc z} := by
  have hR := original_list_predicate_validity_definable W.relations
    (fun I z => I.2.2.Valid hc z) (fun I _ => I.2.2.valid_definable hc)
  have hb := gamma_bijection_validity_definable sp
    (fun _ : Fin W.sourceArity => .rv) (fun _ : Fin W.targetArity => .rv)
    W.source.setSchema.domain.property W.target.setSchema.domain.property W.graph.property
  have h := (F.valid_definable hc).inter ((G.valid_definable hc).inter
    ((W.stabilizer.valid_definable hc).inter (hR.inter ((W.source.valid_definable hc).inter
      ((W.target.valid_definable hc).inter hb)))))
  convert h using 1
  ext z
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ (_ ∧ _) ∧ _ ∧ _ ∧ _)
  constructor
  · rintro ⟨hf, hg, hc, hr, hs, ht, hb⟩
    exact ⟨hf, hg, hc, ⟨hf.1, hr⟩, hs, ht, hb⟩
  · rintro ⟨hf, hg, hc, ⟨_, hr⟩, hs, ht, hb⟩
    exact ⟨hf, hg, hc, hr, hs, ht, hb⟩

theorem RESLayoutStabilizationSchema.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) (z : Fin p → M) (h : W.Valid hc z) :
    nativeRESChartClass (F.chart hc z h.1) = nativeRESChartClass (G.chart hc z h.2.1) := by
  obtain ⟨hf, hg, hc', hr, hs, ht, hbij⟩ := h
  let H : RESExpressionBijectionSchema W.source W.target := ⟨W.graph⟩
  have he := H.native_equality hc z ⟨hs, ht, hbij⟩
  let ev := nativeSchemaEvaluator (B := B) (sp := sp) hc z
  let c := W.stabilizer.nativeValue hc z hc'
  let l := (resCertificateLeftExpression W.relations).2.nativeValue hc z
    (resCertificateLeftExpression_valid hc W.relations z hf.1 hr)
  let r := (resCertificateRightExpression W.relations).2.nativeValue hc z
    (resCertificateRightExpression_valid hc W.relations z hf.1 hr)
  have hevF : ev (FreeCommRing.of ⟨a, F⟩) = nativeRESChartClass (F.chart hc z hf) :=
    (RESExpressionSchema.atom F).formalValue_evaluate hc z hf
  have hevG : ev (FreeCommRing.of ⟨b, G⟩) = nativeRESChartClass (G.chart hc z hg) :=
    (RESExpressionSchema.atom G).formalValue_evaluate hc z hg
  have hevC : ev W.stabilizer.formalValue = c := W.stabilizer.formalValue_evaluate hc z hc'
  have hevL : ev (resCertificateLeftExpression W.relations).2.formalValue = l :=
    (resCertificateLeftExpression W.relations).2.formalValue_evaluate hc z _
  have hevR : ev (resCertificateRightExpression W.relations).2.formalValue = r :=
    (resCertificateRightExpression W.relations).2.formalValue_evaluate hc z _
  have hevS : ev W.source.formalValue = W.source.nativeValue hc z hs := W.source.formalValue_evaluate hc z hs
  have hevT : ev W.target.formalValue = W.target.nativeValue hc z ht := W.target.formalValue_evaluate hc z ht
  have hsPoly := congrArg ev W.source_formal
  have htPoly := congrArg ev W.target_formal
  simp only [map_add, hevF, hevC, hevR, hevS] at hsPoly
  simp only [map_add, hevG, hevC, hevL, hevT] at htPoly
  have hrel : l = r := resCertificateExpressions_native_equality hc W.relations z hf.1 hr
  have hcancel : nativeRESChartClass (F.chart hc z hf) + (c+r) =
      nativeRESChartClass (G.chart hc z hg) + (c+l) := hsPoly.symm.trans (he.trans htPoly)
  rw [hrel] at hcancel
  exact add_right_cancel hcancel

end DiamondIntegral.Section5
