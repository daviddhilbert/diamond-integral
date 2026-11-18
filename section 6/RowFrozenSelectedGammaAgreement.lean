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
import «section 6».RowRVRefinementGammaProducts
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
import «section 6».RowSelectedGammaFormDescent
import «section 6».UnaryParameterFreezing

/-! (Row-form version for Remark 6.20, translated from `FrozenSelectedGammaAgreement`.)
 Freezing every actual Gamma level retains exact agreement with
all local fibre forms after the entire parameter map is updated. Source
points and their precise unary base points are transported explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k d : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (X : SelectedProgramContext η A P C π σ)

theorem baseMap_same_source_row {η' : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    (Y : SelectedProgramContext η' A P C π σ) (p : C) : Y.baseMap p=X.baseMap p :=
  Subtype.ext ((Y.baseMap_value p).trans (X.baseMap_value p).symm)

theorem frozen_source_form_agreement_row
    {W : DefSet (rawMixedSpace (M := M) (n+1) d) S} (D : FMT.FocusFreezingData W)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (Y : SelectedProgramContext (D.unaryParameter hB η) A P C π σ)
    (ζ : ∀ b : B,RowFormOn (A.fibre (unaryFamilyParameter η b)) qR)
    (ω : RowFormOn C qR)
    (hForm : ∀ p : C,rowFormExtension (ζ (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val)
    (hProducts : ∀ γ,∀ E : D.balls,FMT.CoordinateProductDomain
      {p | p ∈ C.carrier ∧ rowFormExtension ω p=γ} (FMT.vfOpenBall E.val) (D.centers E) 0) :
    ∀ p : C,rowFormExtension (ζ (D.unaryBaseFreeze hB (Y.baseMap p)))
      (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val := by
  intro p
  have hMem := FMT.mixedFamilyFreeze_mapsTo D.balls D.centers (0 : Fin (n+1))
    {x | x ∈ C.carrier ∧ rowFormExtension ω x=(ω p).val} D.separated (hProducts (ω p).val)
    (show p.val ∈ {x | x ∈ C.carrier ∧ rowFormExtension ω x=(ω p).val} from
      ⟨p.property,rowFormExtension_at ω p⟩)
  let p' : C := ⟨FMT.mixedFamilyFreeze D.balls D.centers 0 p.val,hMem.1⟩
  have hBase : X.baseMap p'=D.unaryBaseFreeze hB (Y.baseMap p) := by
    apply Subtype.ext
    rw [X.baseMap_value]
    apply Prod.ext
    · funext i
      fin_cases i
      have hOld := congrArg (fun b : B => b.val.1 0) (X.baseMap_same_source_row Y p)
      change (Y.baseMap p).val.1 0=(X.baseMap p).val.1 0 at hOld
      rw [X.baseMap_value] at hOld
      change FMT.vfFamilyFreeze D.balls D.centers (p.val.1 0)=
        FMT.vfFamilyFreeze D.balls D.centers ((Y.baseMap p).val.1 0)
      rw [hOld]
      rfl
    · have h := congrArg Prod.snd (Y.baseMap_value p)
      exact h.symm
  have hLocal : (Fin.tail p'.val.1,p'.val.2 ∘ σ)=(Fin.tail p.val.1,p.val.2 ∘ σ) := by
    apply Prod.ext
    · funext i
      change Function.update p.val.1 0 (FMT.vfFamilyFreeze D.balls D.centers (p.val.1 0)) i.succ=p.val.1 i.succ
      rw [Function.update_of_ne (Fin.succ_ne_zero i)]
    · rfl
  have h := hForm p'
  rw [hBase,hLocal] at h
  have hValue : (ω p').val=(ω p).val := (rowFormExtension_at ω p').symm.trans hMem.2
  exact h.trans hValue

end DiamondIntegral.Section6.SelectedProgramContext
