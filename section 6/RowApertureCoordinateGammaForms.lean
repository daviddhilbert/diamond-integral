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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowPreparedCoverGammaForms
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
import «section 6».RowCoordinateGammaConstancy

/-! (Row-form version for Remark 6.20, translated from `ApertureCoordinateGammaForms`.)
 The actual inverse-transported Gamma maps on aperture branches are
constant in the original active coordinate. The proof recovers source
points, complementary VF coordinates and all old labels literally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem coordinate_step_other_row (D : CentripetalData (G := G) A) (p : A) (i : Fin (n+1)) (hi : i ≠ D.coordinate) :
    (centripetalStepMap D p).val.1 i=p.val.1 i := by
  change (D.point p.val).1 i=p.val.1 i
  simp only [point,Function.update_of_ne hi]

theorem coreGammaForm_at_row (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR)
    (q : D.coreRegularizedImage) (p : A) (he : regularize (D.point p.val)=q.val) :
    rowFormExtension (D.coreGammaFormRow h00 ω) q.val=(ω p).val := by
  rw [rowFormExtension_at]
  change (ω ((centripetalStepMap D).inverse _ ⟨q.val,D.coreRegularizedImage_subset q.property⟩)).val=(ω p).val
  have hf : centripetalStepMap D p=⟨q.val,D.coreRegularizedImage_subset q.property⟩ := Subtype.ext he
  rw [← hf,Map.inverse_apply]

theorem coreGammaForm_coordinate_constant_row
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR) (hSafe : D.CoreFormConstantRow ω) :
    CoordinateGammaConstantRow D.coordinate (D.coreGammaFormRow h00 ω) := by
  intro q q' hOther hTags
  obtain ⟨p,hp,hpCore,he⟩ := (D.mem_coreRegularizedImage h00 q.val).mp q.property
  obtain ⟨p',hp',hpCore',he'⟩ := (D.mem_coreRegularizedImage h00 q'.val).mp q'.property
  let x : A := ⟨p,hp⟩
  let y : A := ⟨p',hp'⟩
  have hx : (centripetalStepMap D x).val=q.val := he
  have hy : (centripetalStepMap D y).val=q'.val := he'
  have hOldTags : p.2=p'.2 := (D.coordinate_step_same_labels_row h00 x y (by
    change (centripetalStepMap D x).val.2=(centripetalStepMap D y).val.2
    rw [hx,hy]
    exact hTags)).1
  have hOldOther (i) (hi : i ≠ D.coordinate) : p.1 i=p'.1 i := by
    rw [← D.coordinate_step_other_row x i hi,← D.coordinate_step_other_row y i hi,hx,hy]
    exact hOther i hi
  have h := hSafe x y hpCore hpCore' hOldOther hOldTags
  rw [← rowFormExtension_at _ q,← rowFormExtension_at _ q']
  rw [D.coreGammaForm_at_row h00 ω q x he,D.coreGammaForm_at_row h00 ω q' y he']
  exact h

theorem releasedGammaForm_coordinate_constant_row
    (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) (hE : E.coordinate=D.coordinate)
    (ω : RowFormOn A qR) (hSafe : D.CoreFormConstantRow ω) :
    CoordinateGammaConstantRow D.coordinate (D.releasedGammaFormRow E h00 ω) := by
  intro q q' hOther hTags
  obtain ⟨p,hp,hpCore,hpNew,he⟩ := (D.mem_releasedRegularizedImage E q.val).mp q.property
  obtain ⟨p',hp',hpCore',hpNew',he'⟩ := (D.mem_releasedRegularizedImage E q'.val).mp q'.property
  let x : A := ⟨p,hp⟩
  let y : A := ⟨p',hp'⟩
  have hx : (centripetalStepMap E x).val=q.val := he
  have hy : (centripetalStepMap E y).val=q'.val := he'
  have hOldTags : p.2=p'.2 := (E.coordinate_step_same_labels_row h00 x y (by
    change (centripetalStepMap E x).val.2=(centripetalStepMap E y).val.2
    rw [hx,hy]
    exact hTags)).1
  have hOldOther (i) (hi : i ≠ D.coordinate) : p.1 i=p'.1 i := by
    have hiE : i ≠ E.coordinate := hE.symm ▸ hi
    rw [← E.coordinate_step_other_row x i hiE,← E.coordinate_step_other_row y i hiE,hx,hy]
    exact hOther i hi
  have h := hSafe x y hpCore hpCore' hOldOther hOldTags
  rw [← rowFormExtension_at _ q,← rowFormExtension_at _ q']
  rw [D.releasedGammaForm_at_row E h00 ω q x he,D.releasedGammaForm_at_row E h00 ω q' y he']
  exact h

end DiamondIntegral.Section6.CentripetalData
