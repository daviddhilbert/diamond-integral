import «section 3».GammaRetainedRelativeMeasuredMaps
import «section 3».GammaRelativeHeadFormulaWitnesses
import «section 3».GammaOriginalBaseHeadTraces

/-! The checked head-row comparison applies to arbitrary mixed
retained-density presentations. Traces and complete Gamma row schemata
are constructed over the original base; no field-base condition remains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem GammaRetainedMeasuredVFData.point_definable (U : GammaRetainedMeasuredVFData hc B (n+1)) :
    GammaSetDefinable B U.domain.carrier :=
  (gammaGroundPointIso (GammaGroundBijection.id U.domain)).target_definable (gammaLogicInput B)

def GammaRetainedMeasuredVFData.pointSet (U : GammaRetainedMeasuredVFData hc B (n+1)) :
    DefSet (M := M) Set.univ (n+1) U.arity := gammaDefSetUniv U.domain.carrier U.point_definable

structure GammaRetainedHeadPreparation (U : GammaRetainedMeasuredVFData hc B (n+1)) where
  head : HeadPreparation U.pointSet
  trace : UniformRelativeTrace Set.univ (n+1) U.pointSet head.target
  gamma : GammaUniformTrace (G := B) trace
  agrees : ∀ p, trace.toMap p = head.map p

namespace GammaRetainedHeadPreparation
variable {U : GammaRetainedMeasuredVFData hc B (n+1)}

theorem targetGamma (T : GammaRetainedHeadPreparation U) : GammaSetDefinable B (carrier T.head.target) :=
  (gammaUniformTraceIso T.trace T.gamma).target_definable (gammaLogicInput B)

def form (T : GammaRetainedHeadPreparation U) :=
  gammaHeadContractedForm T.head T.targetGamma U.labels
    (fun p => U.labels_mem ⟨p.val,p.property⟩) U.form

def schema (T : GammaRetainedHeadPreparation U) (N : ℕ) :=
  gammaMeasuredBoundedSelectedSchema T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
    (headVolumeIndex T.head (Fin.elim0 : Fin 0 → Fin U.arity)) T.form N

theorem exists_original_base
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaRetainedMeasuredVFData hc B (n+1)) : Nonempty (GammaRetainedHeadPreparation U) := by
  obtain ⟨T,_,_,_,_,W,hW,hEq⟩ := gamma_original_base_head_preparation_traced hκ hs h00 hr U.pointSet U.point_definable
  exact ⟨⟨T,W,hW,hEq⟩⟩

end GammaRetainedHeadPreparation

theorem gammaRetained_head_formula_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaRetainedMeasuredVFData hc B (n+1)}
    (F : GammaFullMeasuredBijection U.toMeasured V.toMeasured)
    (hi : ∀ p, ∀ j, j ≠ 0 → (F.map.map p).val.1 j = p.val.1 j)
    (T : GammaRetainedHeadPreparation U) (E : GammaRetainedHeadPreparation V) :
    ∃ NT NE : ℕ,
      (∀ x : Fin n → VF (M := M), (T.schema NT).valid (vfValues x)) ∧
      (∀ x : Fin n → VF (M := M), (E.schema NE).valid (vfValues x)) ∧
      ∀ x : Fin n → VF (M := M), AlgebraicIndependent (vfParameterField B.real) x →
        ∃ H : GammaMeasuredRelationSchema (T.schema NT).essential (E.schema NE).essential, H.valid (vfValues x) := by
  let f := gammaGroundPointMap (A := U.pointSet) (C := V.pointSet) U.point_definable V.point_definable F.map
  have hf : Function.Bijective f := F.map.bijective
  have hΓ : GammaGraphDefinable B (pointMapGraph f) := (gammaGroundPointIso F.map).graph
  have hUnary : UnaryRelative f 0 := hi
  let hF : GammaFullMeasuredBijection
      (gammaPointMeasuredData U.pointSet T.gamma.source U.finite
        (gammaPointRetainedForm U.pointSet T.gamma.source U.labels id (fun p => U.labels_mem ⟨p.val,p.property⟩) U.form))
      (gammaPointMeasuredData V.pointSet E.gamma.source V.finite
        (gammaPointRetainedForm V.pointSet E.gamma.source V.labels id (fun p => V.labels_mem ⟨p.val,p.property⟩) V.form)) := F
  exact gammaRelativeHead_measured_formula_witnesses hκ hs h00 hr hg hv δ hδ hδ1
    T.head E.head T.trace E.trace T.gamma E.gamma T.agrees E.agrees U.finite V.finite
    U.labels V.labels (fun p => U.labels_mem ⟨p.val,p.property⟩) (fun p => V.labels_mem ⟨p.val,p.property⟩)
    U.form V.form hF f hf hΓ (by
      intro p
      change (F.map.map p).val = (f ⟨p.val,p.property⟩).val
      rfl) hUnary

end DiamondIntegral.Section3
