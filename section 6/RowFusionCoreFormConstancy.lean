import «section 6».RowApertureCoordinateGammaForms
import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedCoreFormCompatibility
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaConstancy
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFiniteMeasuredCentripetalPrograms
import «section 6».RowFormCompatibleCarriedCertificates
import «section 6».RowFormCompatibleCarriedPreparation
import «section 6».RowFormCompatibleChainTransport
import «section 6».RowFormCompatibleFocusSteps
import «section 6».RowFormCompatibleRVRefinement
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleTagBranchAssembly
import «section 6».RowFormCompatibleTagChainExtensions
import «section 6».RowFormCompatibleTagComponents
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredBranchFormConstancy
import «section 6».RowMeasuredCentripetalProgramRealizations
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredComplementaryBranchPreparation
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredCoreDimensionInduction
import «section 6».RowMeasuredFormCompatibleCarrying
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPermutedCoordinateBundles
import «section 6».RowMeasuredPreparationSetTransport
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredRVRefinementPreparation
import «section 6».RowMeasuredSynchronizedTargets
import «section 6».RowMeasuredVFConjugatedPreparation
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowMeasuredVariableReleaseInduction
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedMeasuredProgramRealizations
import «section 6».RowPreparedVariableRelease
import «section 6».RowRVRefinementGammaForms
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSemanticGammaBranchDescent
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
import «section 6».RowVFReindexedGammaForms
import «section 6».RowVariableApertureGammaForms
import «section 6».RowMeasuredFusionStepAssembly

/-! (Row-form version for Remark 6.20, translated from `FusionCoreFormConstancy`.)
 Actual local component forms control both the variable old core and
the contracted global core. Equal complementary VF coordinates recover
the identical base point, rather than just an RV-equivalent parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalFusionRepair
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (R : CentripetalFusionRepair (G := G) η T K A P C π σ)

def localSourcePointRow (p : C) : A.fibre (unaryFamilyParameter R.parameter (R.context.baseMap p)) :=
  ⟨(Fin.tail p.val.1,p.val.2 ∘ σ),by
    obtain ⟨b,hb,hA⟩ := (mem_unaryIndexedMixedFamily R.parameter A _).mp (R.context.source p.val p.property)
    have hBase : b=R.context.baseMap p := Subtype.ext
      (hb.symm.trans ((selectedJointPoint_base π σ p.val).trans (R.context.baseMap_value p).symm))
    rw [hBase] at hA
    rwa [selectedJointPoint_local] at hA⟩

theorem baseMap_eq_of_complement_row
    (p z : C) (hOther : ∀ i,i ≠ R.component.coordinate → p.val.1 i=z.val.1 i) (hTags : p.val.2=z.val.2) :
    R.context.baseMap p=R.context.baseMap z := by
  apply Subtype.ext
  rw [R.context.baseMap_value,R.context.baseMap_value]
  apply Prod.ext
  · funext i
    exact hOther 0 (by rw [R.coordinate]; exact (Fin.succ_ne_zero _).symm)
  · exact congrArg (fun u => u ∘ π) hTags

theorem oldRadius_le_global_cutoff_row
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (p : C) (hu : p.val.2 ∈ R.component.activeTags.carrier) :
    (R.oldRadius p.val.2).val ≤ vfValue (R.component.coefficient*R.component.extendedFocus p.val) := by
  rw [R.oldRadius_value hCoeffMem ⟨p.val,p.property,hu⟩,R.focus p]
  change vfValue ((R.fibreComponents.component (R.context.baseMap p)).coefficient*
      (R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)) ≤
    vfValue (R.component.coefficient*
      (R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ))
  calc
    _ = vfValue (R.fibreComponents.component (R.context.baseMap p)).coefficient*
        vfValue ((R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)) :=
      Values.vfValueHom.map_mul _ _
    _ ≤ vfValue R.component.coefficient*
        vfValue ((R.fibreComponents.component (R.context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)) :=
      mul_le_mul_left (R.coefficient (R.context.baseMap p)) _
    _ = _ := (Values.vfValueHom.map_mul _ _).symm

theorem variable_core_form_constant_of_local_forms_row
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter R.parameter b)) qR)
    (hζ : ∀ b,(R.fibreComponents.component b).CoreFormConstantRow (ζ b))
    (ω : RowFormOn C qR)
    (hForm : ∀ p : C,rowFormExtension (ζ (R.context.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    R.component.VariableCoreFormConstantRow R.oldRadius ω := by
  intro p z hpAct hzAct hpOld hzOld hOther hTags
  have hBase : R.context.baseMap z=R.context.baseMap p := (R.baseMap_eq_of_complement_row p z hOther hTags).symm
  let b := R.context.baseMap p
  let x := R.localSourcePointRow p
  let y : A.fibre (unaryFamilyParameter R.parameter b) :=
    ⟨(Fin.tail z.val.1,z.val.2 ∘ σ),by
      have hz := (R.localSourcePointRow z).property
      change (Fin.tail z.val.1,z.val.2 ∘ σ) ∈ (A.fibre (unaryFamilyParameter R.parameter (R.context.baseMap z))).carrier at hz
      rw [hBase] at hz
      exact hz⟩
  have hpCore : (R.fibreComponents.component (R.context.baseMap p)).core (Fin.tail p.val.1,p.val.2 ∘ σ)=true := by
    rw [R.oldRadius_value hCoeffMem ⟨p.val,p.property,hpAct⟩,R.focus p,R.coordinate,
      ← R.fibreComponents.coordinate (R.context.baseMap p)] at hpOld
    exact decide_eq_true hpOld
  have hzCore : (R.fibreComponents.component (R.context.baseMap z)).core (Fin.tail z.val.1,z.val.2 ∘ σ)=true := by
    rw [R.oldRadius_value hCoeffMem ⟨z.val,z.property,hzAct⟩,R.focus z,R.coordinate,
      ← R.fibreComponents.coordinate (R.context.baseMap z)] at hzOld
    exact decide_eq_true hzOld
  rw [hBase] at hzCore
  have hLocalOther (i) (hi : i ≠ (R.fibreComponents.component b).coordinate) : x.val.1 i=y.val.1 i := by
    have hiK : i ≠ K.coordinate := fun h => hi (h.trans (R.fibreComponents.coordinate b).symm)
    apply hOther i.succ
    rw [R.coordinate]
    simpa only [ne_eq,Fin.succ_inj] using hiK
  have hLocal := hζ b x y hpCore hzCore hLocalOther (congrArg (fun u => u ∘ σ) hTags)
  have hzForm := hForm z
  rw [hBase] at hzForm
  have hLocalExt := (rowFormExtension_at (ζ b) x).trans (hLocal.trans (rowFormExtension_at (ζ b) y).symm)
  exact (hForm p).symm.trans (hLocalExt.trans hzForm)

end CentripetalFusionRepair

namespace CentripetalData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem VariableCoreFormConstantRow.core_of_cutoff_row {D : CentripetalData (G := G) A}
    {ρ : (Fin r → RVInfinity M) → Gamma M}
    {ω : RowFormOn A qR} (h : D.VariableCoreFormConstantRow ρ ω)
    (hDom : ∀ p : A,p.val.2 ∈ D.activeTags.carrier → (ρ p.val.2).val ≤ vfValue (D.coefficient*D.extendedFocus p.val)) :
    D.CoreFormConstantRow ω := by
  intro p q hp hq hOther hTags
  have hpA := D.core_true_active p.val hp
  have hqA := D.core_true_active q.val hq
  exact h p q hpA hqA ((hDom p hpA).trans_lt (of_decide_eq_true hp))
    ((hDom q hqA).trans_lt (of_decide_eq_true hq)) hOther hTags

end CentripetalData
end DiamondIntegral.Section6
