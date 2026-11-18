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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormFreezing
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowRVRefinementGammaDescent
import «section 6».RowRVRefinementGammaForms
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
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
import «section 6».RowRVRefinementGammaProducts
import «section 6».SelectedProgramBaseMaps

/-! (Row-form version for Remark 6.20, translated from `SelectedGammaFormDescent`.)
 Exact agreement with the local fibre forms gives actual original-base
Gamma descent to the covered joint source. The complete graph and open
levels descend through the actual source map, without naming local forms
or choosing a Gamma representative as a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
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
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (X : SelectedProgramContext η A P C π σ)

theorem baseMap_eq_of_selected_joint_eq_row (p z : C)
    (he : selectedJointPoint π σ p.val=selectedJointPoint π σ z.val) : X.baseMap p=X.baseMap z := by
  apply Subtype.ext
  exact ((X.baseMap_value p).trans (selectedJointPoint_base π σ p.val).symm).trans
    ((congrArg unaryFamilyBasePoint he).trans ((selectedJointPoint_base π σ z.val).trans (X.baseMap_value z).symm))

theorem gamma_constant_on_joint_fibres_row
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR)
    (ω : RowFormOn C qR)
    (hForm : ∀ p : C,rowFormExtension (ζ (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val)
    (p z : C) (he : selectedJointPoint π σ p.val=selectedJointPoint π σ z.val) : (ω p).val=(ω z).val := by
  have hBase := X.baseMap_eq_of_selected_joint_eq_row p z he
  have hLocal : (Fin.tail p.val.1,p.val.2 ∘ σ)=(Fin.tail z.val.1,z.val.2 ∘ σ) := by
    have h := congrArg (fun w : Mixed M (n+1) (r+s) => (Fin.tail w.1,w.2 ∘ Fin.natAdd r)) he
    rw [selectedJointPoint_local,selectedJointPoint_local] at h
    exact h
  have hp := hForm p
  rw [hBase,hLocal] at hp
  exact hp.symm.trans (hForm z)

def coveredGammaFormRow
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR)
    (ω : RowFormOn C qR)
    (hForm : ∀ p : C,rowFormExtension (ζ (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    RowFormOn (X.jointFrame hTag).coveredBase qR :=
  (X.jointFrame hTag).descendedGammaFormRow ω (X.gamma_constant_on_joint_fibres_row ζ ω hForm)

theorem coveredGammaForm_at_row
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR)
    (ω : RowFormOn C qR)
    (hForm : ∀ p : C,rowFormExtension (ζ (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) (p : C) :
    X.coveredGammaFormRow hTag ζ ω hForm ((X.jointFrame hTag).oldMap.toImage p)=ω p :=
  (X.jointFrame hTag).descendedGammaForm_at_row ω _ p

theorem coveredGammaForm_levels_open_row
    (hTag : ∀ p ∈ (unaryIndexedMixedFamily η A).carrier,∀ z ∈ (unaryIndexedMixedFamily η A).carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR)
    (ω : RowFormOn C qR)
    (hForm : ∀ p : C,rowFormExtension (ζ (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ C.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ (X.jointFrame hTag).coveredBase.carrier ∧
      rowFormExtension (X.coveredGammaFormRow hTag ζ ω hForm) (x,u)=γ} :=
  (X.jointFrame hTag).descendedGammaForm_levels_open_row ω _ hLevels

end DiamondIntegral.Section6.SelectedProgramContext
