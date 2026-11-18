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
import «section 6».RowMeasuredFormCompatibleTargets
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
import «section 6».RowSelectedMeasuredTerminalPreparation

/-! (Row-form version for Remark 6.20, translated from `SelectedMeasuredRegularizationTerminal`.)
 A terminal regularization prepares all actual protected images and
makes the full ambient form constant on output labels. The complete
Gamma row compares parameters with the same retained base labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

theorem measured_regularization_terminal_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hBRP : IsRVPullback B.carrier)
    (U : UniformMeasuredProgramFamilyRow (G := G) η (.regularize s) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : RowFormOn C qR)
    (hSource : ∀ p : C,rowFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∃ F : MeasuredCoordinatePreparationRow (G := G) C
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
        (fun i => rvLabelPullback_subset C _ _) ω,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) C F.target F.map
        (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))) ω := by
  let Q (i) := rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))
  have hQC (i) : (Q i).carrier ⊆ C.carrier := rvLabelPullback_subset C _ _
  have hPA := fun b => (U.geometry b).subset
  let Y := X.afterRegularization h00 hc hκ hs hv hPA
  let F := Y.finish (G := G) hBRP U.toUniformProgramFamily.prepared_target_fibres
    (fun i => U.rows _ ((CentripetalProgramTemplate.regularize _).terminal_piece_data_mem A P i))
  let R (i) := rvLabelPullback (regularizeMap C).image
    (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
    (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i)))
  have hRC (i) : (R i).carrier ⊆ (regularizeMap C).image.carrier := rvLabelPullback_subset _ _ _
  have hPrepared (i) : IsRVPullback ((regularization C).restrict (hQC i)).image.carrier := by
    have h := F.prepared i
    have hIdentity : (F.map.restrict (hRC i)).image.carrier=(R i).carrier := by
      ext z
      exact ⟨fun ⟨p,hp⟩ => hp ▸ p.property,fun hp => ⟨⟨z,hp⟩,rfl⟩⟩
    rw [hIdentity] at h
    dsimp only [R] at h
    rw [regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base] at h
    exact h
  have hChain : SynchronizedCentripetalChain (G := G) (Fin k) C (regularizeMap C).image (regularization C) Q :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i))
  let J : PreparedSynchronizedFamily (G := G) C Q hQC := {
    arity := (n+1)+q
    target := (regularizeMap C).image
    map := regularization C
    chain := hChain
    proper := regularization_properInvariant h00 hc hκ hs hv C X.proper X.doublyBounded
    doublyBounded := regularized_vfDoublyBounded X.doublyBounded
    pullback := regularization_rvPullback C X.pullback
    prepared := hPrepared }
  have hPhi : FormCompatibleSynchronizedChainRow (G := G) (Fin k) C J.target J.map Q ω :=
    .regularize C X.proper X.doublyBounded Q hQC X.piecesProper (fun i => X.doublyBounded.mono (hQC i)) ω
  apply J.measured_form_compatible_target_row h00 hc hκ hs hv ω hPhi
  intro p z hTags
  change (regularize p.val).2=(regularize z.val).2 at hTags
  have hOldTags : p.val.2=z.val.2 := by
    funext i
    have h := congrFun hTags (Fin.natAdd (n+1) i)
    change (regularize p.val).2 (Fin.natAdd (n+1) i)=(regularize z.val).2 (Fin.natAdd (n+1) i) at h
    simpa only [regularize,Fin.append_right] using h
  let b := X.baseMap p
  let c := X.baseMap z
  let x := X.localSourcePointRow p
  let y := X.localSourcePointRow z
  have hLocalTags : (regularization (A.fibre (unaryFamilyParameter η b)) x).val.2=
      (regularization (A.fibre (unaryFamilyParameter η c)) y).val.2 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have h := congrFun hTags (Fin.castAdd q j.succ)
      simp only [regularize,Fin.append_left] at h
      simp only [regularization_apply,regularize,Fin.append_left]
      change rv M (p.val.1 j.succ)=rv M (z.val.1 j.succ)
      exact h
    · simp only [regularization_apply,regularize,Fin.append_right]
      change p.val.2 (σ j)=z.val.2 (σ j)
      exact congrFun hOldTags (σ j)
  have hValue := U.values_eq_of_transition_labels_row b c (X.baseMap_labels p z hOldTags)
    (regularization (A.fibre (unaryFamilyParameter η b))) (regularization_bijective _)
    (regularization (A.fibre (unaryFamilyParameter η c))) (regularization_bijective _)
    (regularizationParameterTransition_at A _) (regularizationParameterTransition_at A _) x y hLocalTags
  have hExt := (rowFormExtension_at (U.forms b) x).trans
    (hValue.trans (rowFormExtension_at (U.forms c) y).symm)
  exact (hSource p).symm.trans (hExt.trans (hSource z))

end DiamondIntegral.Section6.SelectedProgramContext
