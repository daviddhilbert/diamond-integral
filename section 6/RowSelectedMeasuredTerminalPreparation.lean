import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreComponentSemantics
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaRVTraceValues
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSequentialMeasuredCentripetalPrograms
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
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowUniformMeasuredTerminalValues
import «section 6».SelectedProgramPrefixes
import «section 6».RowMeasuredFormCompatibleTargets

/-! (Row-form version for Remark 6.20, translated from `SelectedMeasuredTerminalPreparation`.)
 Terminal identity preparation uses the entire Gamma record to
compare different head parameters. The actual source map, every protected
image and the form-compatible ambient chain are constructed together. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

namespace SelectedProgramContext

def localSourcePointRow (X : SelectedProgramContext η A P C π σ) (p : C) :
    A.fibre (unaryFamilyParameter η (X.baseMap p)) :=
  ⟨(Fin.tail p.val.1,p.val.2 ∘ σ),by
    obtain ⟨b,hb,hA⟩ := (mem_unaryIndexedMixedFamily η A _).mp (X.source p.val p.property)
    have hBase : b=X.baseMap p := Subtype.ext
      (hb.symm.trans ((selectedJointPoint_base π σ p.val).trans (X.baseMap_value p).symm))
    rw [hBase] at hA
    rwa [selectedJointPoint_local] at hA⟩

theorem measured_identity_terminal_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hBRP : IsRVPullback B.carrier)
    (U : UniformMeasuredProgramFamilyRow (G := G) η (.identity s) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : RowFormOn C qR)
    (hSource : ∀ p : C,rowFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∃ F : MeasuredCoordinatePreparationRow (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) C F.target F.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let J := X.terminal (G := G) hBRP U.toUniformProgramFamily
  have hPhi : FormCompatibleSynchronizedChainRow (G := G) (Fin k) C J.target J.map
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω :=
    .identity C X.proper _ (fun i => rvLabelPullback_subset C _ _) X.piecesProper ω
  apply J.measured_form_compatible_target_row h00 hc hκ hs hv ω hPhi
  intro p z hTags
  let b := X.baseMap p
  let c := X.baseMap z
  let x := X.localSourcePointRow p
  let y := X.localSourcePointRow z
  have hOldTags : p.val.2=z.val.2 := hTags
  have hValue := U.values_eq_of_transition_labels_row b c (X.baseMap_labels p z hOldTags)
    (Map.id (A.fibre (unaryFamilyParameter η b))) Function.bijective_id
    (Map.id (A.fibre (unaryFamilyParameter η c))) Function.bijective_id
    (identityParameterTransition_at A _) (identityParameterTransition_at A _) x y
    (congrArg (fun u => u ∘ σ) hOldTags)
  have hExt := (rowFormExtension_at (U.forms b) x).trans
    (hValue.trans (rowFormExtension_at (U.forms c) y).symm)
  exact (hSource p).symm.trans (hExt.trans (hSource z))

end SelectedProgramContext
end DiamondIntegral.Section6
