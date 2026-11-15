import «section 5».NativeDegreeTaggedLayouts
import «section 5».NativeRelationListPresentations
import «section 5».RESLayoutStabilization
import «section 5».RESFixedBijectionPromotion
import «section 5».RESLiteralFamilyCriterion

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



def presentedRootSchema (z : Fin p → M) (F : RESSetSchema B p a sp) (hF : F.Valid hc z) :
    PresentedGradedRESObjectAt (hc := hc) B sp z :=
  ⟨⟨a, Section3RVChartBridge.nativeRES hc (F.chart hc z hF)⟩,
    ⟨a, .atom F, hF, (Section3RVRoundtripBridge.native_chart (F.object hc z hF).obj).symm⟩⟩

theorem presented_tagged_layout_for (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (L : List (PresentedGradedRESObjectAt (hc := hc) B sp z))
    (A : List (GradedObject hc ⟨B.real ∪ Set.range z, B.gamma⟩)) (hA : presentedOldObjects L = A)
    (N : ℕ) (hd : ∀ U ∈ A, U.1 < N) :
    ∃ P : NativeDomainPresentationAt B sp z
      (taggedRVFinFamily hc ⟨B.real ∪ Set.range z, B.gamma⟩ N
        (fun i => actualFamilyDegreeDomain A i.val)).2,
      P.expression.formalValue = presentedFormalSum L := by
  subst A
  apply presented_degree_tagged_expression_exists B sp z hz L N
  intro U hU
  apply hd U.1
  exact List.mem_map.mpr ⟨U, hU, rfl⟩

theorem res_layout_schema_of_literal_witness
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (hF : F.Valid hc z) (hG : G.Valid hc z)
    (w : LiteralFamilyWitness hc ⟨B.real ∪ Set.range z, B.gamma⟩ (F.chart hc z hF) (G.chart hc z hG)) :
    ∃ W : RESLayoutStabilizationSchema F G, W.Valid hc z := by
  obtain ⟨C, hC⟩ := native_presented_list_exists B sp z hz w.stabilizer
  obtain ⟨R⟩ := native_relation_list_presentation_exists B sp z hz w.terms
  let L := presentedRootSchema z F hF :: (C ++ R.right)
  let T := presentedRootSchema z G hG :: (C ++ R.left)
  have hL : presentedOldObjects L = w.toActual.leftTotal := by
    change _ :: presentedOldObjects (C ++ R.right) = _
    rw [presentedOldObjects_append, hC, R.right_old]
    rfl
  have hT : presentedOldObjects T = w.toActual.rightTotal := by
    change _ :: presentedOldObjects (C ++ R.left) = _
    rw [presentedOldObjects_append, hC, R.left_old]
    rfl
  have hdL : ∀ U ∈ w.toActual.leftTotal, U.1 < w.toActual.degreeCount := by
    intro U hU
    exact positiveFamilyBound_left hc _ _ _ U.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨U, hU, rfl⟩))
  have hdT : ∀ U ∈ w.toActual.rightTotal, U.1 < w.toActual.degreeCount := by
    intro U hU
    exact positiveFamilyBound_right hc _ _ _ U.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨U, hU, rfl⟩))
  obtain ⟨S, hS⟩ := presented_tagged_layout_for B sp z hz L w.toActual.leftTotal hL w.toActual.degreeCount hdL
  obtain ⟨D, hD⟩ := presented_tagged_layout_for B sp z hz T w.toActual.rightTotal hT w.toActual.degreeCount hdT
  let f := D.bijection.symm.comp (w.taggedBijection.comp S.bijection)
  obtain ⟨H, _, _, hH⟩ := res_expression_bijection_schema_at_parameter B sp z hz
    S.expression D.expression S.valid D.valid f
  let E := presentedCoefficientExpression C
  have hSF : S.expression.formalValue = FreeCommRing.of ⟨a,F⟩ +
      (E.2.formalValue + (resCertificateRightExpression R.certificates).2.formalValue) := by
    rw [hS]
    change FreeCommRing.of ⟨a,F⟩ + presentedFormalSum (C ++ R.right) = _
    rw [presentedFormalSum_append, R.right_formal, presentedCoefficientExpression_formal]
  have hDF : D.expression.formalValue = FreeCommRing.of ⟨b,G⟩ +
      (E.2.formalValue + (resCertificateLeftExpression R.certificates).2.formalValue) := by
    rw [hD]
    change FreeCommRing.of ⟨b,G⟩ + presentedFormalSum (C ++ R.left) = _
    rw [presentedFormalSum_append, R.left_formal, presentedCoefficientExpression_formal]
  let W : RESLayoutStabilizationSchema F G := {
    stabilizerArity := E.1
    stabilizer := E.2
    relations := R.certificates
    sourceArity := S.arity
    targetArity := D.arity
    source := S.expression
    target := D.expression
    source_formal := hSF
    target_formal := hDF
    graph := H.graph }
  exact ⟨W, hF, hG, presentedCoefficientExpression_valid C hz, R.valid, S.valid, D.valid, hH⟩

theorem res_layout_schema_exists_of_native_equality
    (B : Base (M := M)) (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
    (hF : F.Valid hc z) (hG : G.Valid hc z)
    (he : nativeRESChartClass (F.chart hc z hF) = nativeRESChartClass (G.chart hc z hG)) :
    ∃ W : RESLayoutStabilizationSchema F G, W.Valid hc z := by
  obtain ⟨w⟩ := (res_equality_iff_literal_family_witness hc _ (F.chart hc z hF) (G.chart hc z hG)).mp he
  exact res_layout_schema_of_literal_witness B sp z hz F G hF hG w

end DiamondIntegral.Section5
