import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».RowGammaRVTraceValues
import «section 6».RowExactGammaTransport

/-! (Row-form version for Remark 6.20, translated from `MeasuredProgramRVTraces`.)
 The complete geometric program trace is extended by its entire
terminal Gamma graph in RV. Each individual admissible row is bounded
using actual source-form bounds, without a uniform VF-parameter bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CentripetalProgramTemplate.gammaRVTraceRow (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    RVSetParameterTemplate (M := M) S p (s+qR) := (W.transportRow (T.transition A)).rvTrace

def CentripetalProgramTemplate.measuredRVTraceRow (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    List (RVDataTemplate (M := M) S p) := T.rvTrace A P ++ [⟨s+qR,T.gammaRVTraceRow A W⟩]

theorem CentripetalProgramTemplate.gammaRVTrace_mem_row
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) :
    (⟨s+qR,T.gammaRVTraceRow A W⟩ : RVDataTemplate (M := M) S p) ∈ T.measuredRVTraceRow A P W :=
  List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem CentripetalProgramTemplate.gammaRVTrace_bounded_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (h : TemplateFibreGeometry A P a)
    (ω : RowFormOn (A.fibre a) qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ rowFormExtension ω (x,u)=γ}) :
    RVValueDoublyBounded ((T.gammaRVTraceRow A W).fibre a).carrier := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha h.proper h.doublyBounded h.subset h.piecesProper
  have hf := F.chain.toChain.toSpecial.bijective h00
  let η := ω.comp (F.map.inverse hf)
  have hGraph := gammaTransitionImage_at_row a (T.transition A).graph W.graph F.map hf ω F.graph hW
  have hTarget := F.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
  apply (W.transportRow (T.transition A)).rvTrace_doublyBounded_of_bounds_row a η hGraph hTarget.rvBounded
  obtain ⟨δ,hδ⟩ := gammaForm_value_bounds_row h00 hc linear hκ hs hv (small_union_range hκ.le S hsmall a)
    (hΓ.mono Set.subset_union_left (Set.Subset.rfl)) h.proper ω hLevels
  exact ⟨δ,fun q => hδ (F.map.inverse hf q)⟩

theorem CentripetalProgramTemplate.measuredRVTrace_bounded_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (h : TemplateFibreGeometry A P a)
    (ω : RowFormOn (A.fibre a) qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (A.fibre a).carrier ∧ rowFormExtension ω (x,u)=γ}) :
    RVTraceRowsBounded a (T.measuredRVTraceRow A P W) := by
  apply rvTraceRowsBounded_append a (T.rvTrace_bounded h00 hc hκ hs hv A P a ha h)
  intro D hD
  have he : D=(⟨s+qR,T.gammaRVTraceRow A W⟩ : RVDataTemplate (M := M) S p) := List.mem_singleton.mp hD
  subst D
  exact T.gammaRVTrace_bounded_row h00 hc linear hκ hs hv hsmall hΓ A P W a ha h ω hW hLevels

end DiamondIntegral.Section6
