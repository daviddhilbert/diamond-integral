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
import «section 6».RowMeasuredProgramPrefixLoci
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSelectedMeasuredTerminalPreparation
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
import «section 6».RowUniformMeasuredProgramPrefixes
import «section 6».RowUniformMeasuredTerminalValues
import «section 6».RowSelectedMeasuredRegularizationTerminal
import «section 6».RowUniformMeasuredPrefixValues
import «section 6».RowMeasuredPreparationTransport

/-! (Row-form version for Remark 6.20, translated from `MeasuredSelectedProgramPrefixes`.)
 Identity and regularization prefixes preserve the precise agreement
between the actual ambient form and the remaining local forms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

def regularizationGammaFormRow
    (ω : RowFormOn C qR) :
    RowFormOn (regularizeMap C).image qR :=
  ω.comp ((regularization C).inverse (regularization_bijective C))

theorem regularizationGammaForm_transport_row
    (ω : RowFormOn C qR) (p : C) :
    (regularizationGammaFormRow ω (regularization C p)).val=(ω p).val := by
  change (ω ((regularization C).inverse _ (regularization C p))).val=(ω p).val
  rw [Map.inverse_apply]

theorem afterIdentity_source_form_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {H : CentripetalProgramTemplate (M := M) S 1 n s t}
    (U : UniformMeasuredProgramFamilyRow (G := G) η ((CentripetalProgramTemplate.identity s).comp H) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : RowFormOn C qR)
    (hSource : ∀ p : C,rowFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∀ p : C,rowFormExtension ((U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
      ((X.afterIdentity (fun b => (U.geometry b).subset)).baseMap p))
      (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val := by
  intro p
  let b := X.baseMap p
  let x := X.localSourcePointRow p
  let y : ((CentripetalProgramTemplate.identity s).target A).fibre (unaryFamilyParameter η b) :=
    ⟨x.val,by
      change x.val ∈ (((CentripetalProgramTemplate.identity s).pieceTarget A A).fibre _).carrier
      rw [identity_pieceTarget_fibre A A _ (Set.Subset.refl _)]
      exact x.property⟩
  have hBase : (X.afterIdentity (fun b => (U.geometry b).subset)).baseMap p=b := by
    apply Subtype.ext
    exact (SelectedProgramContext.baseMap_value _ p).trans (X.baseMap_value p).symm
  have h := U.afterPrefix_value_row h00 hc linear hκ hs hv hsmall hΓ b (Map.id (A.fibre _))
    Function.bijective_id (identityParameterTransition_at A _) x y rfl
  rw [hBase]
  exact (rowFormExtension_at _ y).trans (h.trans ((rowFormExtension_at (U.forms b) x).symm.trans (hSource p)))

theorem afterRegularization_source_form_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {H : CentripetalProgramTemplate (M := M) S 1 n (n+s) t}
    (U : UniformMeasuredProgramFamilyRow (G := G) η ((CentripetalProgramTemplate.regularize s).comp H) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : RowFormOn C qR)
    (hSource : ∀ p : C,rowFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∀ z : (regularizeMap C).image,rowFormExtension ((U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
      ((X.afterRegularization h00 hc hκ hs hv (fun b => (U.geometry b).subset)).baseMap z))
      (Fin.tail z.val.1,z.val.2 ∘ regularizedTailLabels σ)=(regularizationGammaFormRow ω z).val := by
  intro z
  obtain ⟨p,hp⟩ := z.property
  have hz : z=regularization C p := Subtype.ext hp.symm
  subst z
  let b := X.baseMap p
  let x := X.localSourcePointRow p
  let y : ((CentripetalProgramTemplate.regularize s).target A).fibre (unaryFamilyParameter η b) :=
    ⟨regularize x.val,by
      exact (regularization_pieceTarget_mem_iff A A _ (Set.Subset.refl _) x.val).mpr x.property⟩
  have hBase : (X.afterRegularization h00 hc hκ hs hv (fun b => (U.geometry b).subset)).baseMap
      (regularization C p)=b := by
    apply Subtype.ext
    rw [SelectedProgramContext.baseMap_value,X.baseMap_value,regularization_apply]
    exact selectedUnaryBasePoint_regularize π p.val
  have hLocal : (Fin.tail (regularization C p).val.1,
      (regularization C p).val.2 ∘ regularizedTailLabels σ)=regularize x.val := by
    have h := regularized_selected_tail π σ p.val
    rw [selectedJointPoint_local] at h
    exact h
  have h := U.afterPrefix_value_row h00 hc linear hκ hs hv hsmall hΓ b (regularization (A.fibre _))
    (regularization_bijective _) (regularizationParameterTransition_at A _) x y rfl
  rw [hBase,hLocal,regularizationGammaForm_transport_row]
  exact (rowFormExtension_at _ y).trans (h.trans ((rowFormExtension_at (U.forms b) x).symm.trans (hSource p)))

end DiamondIntegral.Section6.SelectedProgramContext
