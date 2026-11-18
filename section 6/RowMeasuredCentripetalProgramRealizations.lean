import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowFiniteMeasuredCentripetalPrograms

/-! (Row-form version for Remark 6.20, translated from `MeasuredCentripetalProgramRealizations`.)
 A measured-admissible finite program realizes its actual
transported Gamma form, with exact equality everywhere and constancy on
its full output RV-label fibres. Its chain and every restriction remain
those of the original program realization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramRealization.transported_gamma_form_row
    (h00 : M ⊨ Axioms.ACVF00)
    {T : CentripetalProgramTemplate (M := M) S p n r s}
    {A : MixedSetParameterTemplate (M := M) S p n r}
    {P : Fin k → MixedSetParameterTemplate (M := M) S p n r} {a : Fin p → M}
    (F : CentripetalProgramRealization (G := G) T A P a)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (ha : a ∈ T.measuredGoodRow A P W)
    (ω : RowFormOn (A.fibre a) qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph) :
    ∃ η : RowFormOn ((T.target A).fibre a) qR,
      (∀ t : A.fibre a,(η (F.map t)).val=(ω t).val) ∧
      ∀ x y : (T.target A).fibre a,x.val.2=y.val.2 → (η x).val=(η y).val := by
  have hBij := F.chain.toChain.toSpecial.bijective h00
  let η := ω.comp (F.map.inverse hBij)
  have hConst := (gammaTransitionConstantParameterLocus_iff_row a _ _ F.map ω F.graph hW).mp ha.2
  refine ⟨η,?_,?_⟩
  · intro t
    change (ω (F.map.inverse hBij (F.map t))).val=(ω t).val
    rw [Map.inverse_apply]
  · intro x y hxy
    apply hConst (F.map.inverse hBij x) (F.map.inverse hBij y)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hxy

theorem CentripetalProgramTemplate.exists_measured_realization_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.measuredGoodRow A P W) (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier)
    (ω : RowFormOn (A.fibre a) qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph) :
    ∃ F : CentripetalProgramRealization (G := G) T A P a,
      ∃ η : RowFormOn ((T.target A).fibre a) qR,
        (∀ t : A.fibre a,(η (F.map t)).val=(ω t).val) ∧
        ∀ x y : (T.target A).fibre a,x.val.2=y.val.2 → (η x).val=(η y).val := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha.1.1 hA hAD hPA hP
  obtain ⟨η,hη,hConst⟩ := F.transported_gamma_form_row h00 W ha ω hW
  exact ⟨F,η,hη,hConst⟩

end DiamondIntegral.Section6
