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
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleRVRefinement
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleTagBranchAssembly
import «section 6».RowFormCompatibleTagChainExtensions
import «section 6».RowFormCompatibleTagComponents
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreComponentSemantics
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormFreezing
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaRVTraceValues
import «section 6».RowGammaTransitionImages
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
import «section 6».RowMeasuredFusionStepAssembly
import «section 6».RowMeasuredIndexedFocusRepair
import «section 6».RowMeasuredPermutedCoordinateBundles
import «section 6».RowMeasuredPreparationSetTransport
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredRVRefinementPreparation
import «section 6».RowMeasuredSynchronizedTargets
import «section 6».RowMeasuredUnaryBaseFocusFreezing
import «section 6».RowMeasuredVFConjugatedPreparation
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowMeasuredVariableReleaseInduction
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedMeasuredProgramRealizations
import «section 6».RowPreparedVariableRelease
import «section 6».RowRVRefinementGammaDescent
import «section 6».RowRVRefinementGammaForms
import «section 6».RowRVRefinementGammaProducts
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSelectedGammaFormDescent
import «section 6».RowSemanticGammaBranchDescent
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
import «section 6».RowVFReindexedGammaForms
import «section 6».RowVariableApertureGammaForms
import «section 6».CentripetalFusionRepairs
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowMeasuredSelectedIndexedFocusRepair
import «section 6».RowFrozenSelectedGammaAgreement
import «section 6».RowFusionCoreFormConstancy
import «section 6».RowTemplateComponentGammaGuards

/-! (Row-form version for Remark 6.20, translated from `MeasuredCentripetalFusionRepairs`.)
 A full actual fusion repair retains the measured program family and
exact source-form agreement after continuity repair. The semantic form
conditions for its old and new apertures are derived from its actual
local component guards. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

structure MeasuredCentripetalFusionRepairRow
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : CentripetalProgramTemplate (M := M) S 1 n s t)
    (K : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q)
    (ω : RowFormOn C qR) where
  geometric : CentripetalFusionRepair (G := G) η T K A P C π σ
  family : UniformMeasuredProgramFamilyRow (G := G) geometric.parameter T A P W
  sourceForm : ∀ p : C,rowFormExtension (family.forms (geometric.context.baseMap p))
    (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val
  firstCore : ∀ b : B,unaryFamilyParameter geometric.parameter b ∈
    (CentripetalProgramTemplate.centripetal K).coreFormGoodRow A W

theorem exists_measured_centripetal_fusion_repair_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {T : CentripetalProgramTemplate (M := M) S 1 n s t}
    {K : FocusComponentParameterTemplate (M := M) S 1 n s}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
    {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
    (hB : ProperInvariant S B.carrier) (hBRP : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (U : UniformMeasuredProgramFamilyRow (G := G) η T A P W) (X : SelectedProgramContext η A P C π σ)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ K.good A P)
    (hActiveMem : (⟨n+s,leadingRVImageTemplate (focusActiveParameterTemplate A K.active)⟩ : RVDataTemplate S 1)
      ∈ T.rvTrace A P)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P)
    (ω : RowFormOn C qR)
    (hSourceForm : ∀ p : C,rowFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ C.carrier ∧ rowFormExtension ω (x,u)=γ})
    (hCore : ∀ b : B,unaryFamilyParameter η b ∈ (CentripetalProgramTemplate.centripetal K).coreFormGoodRow A W) :
    Nonempty (MeasuredCentripetalFusionRepairRow (G := G) η T K A P W C π σ ω) := by
  let hTag := U.toUniformProgramFamily.component_joint_tagged K hGood hBTag
  let Y := X.jointFrame hTag
  have hL := Y.coveredBase_properInvariant h00 hc hκ hs hv X.pullback
  let hActiveRows := U.rows _ hActiveMem
  let F := selectedIndexedFocusGraph (G := G) hv K Y X.pullback hBRP hBTag hGood U.pullback
    U.toUniformProgramFamily.initial_rows hActiveRows hL
  have hSame : ∀ p q : Y.base,(Y.oldPoint p).val=(Y.oldPoint q).val → (ω p).val=(ω q).val :=
    X.gamma_constant_on_joint_fibres_row U.forms ω hSourceForm
  obtain ⟨R,hCoveredProducts,hProducts⟩ := exists_measured_selected_indexed_focus_repair_row h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    Y X.pullback hB X.piecesProper F ω hSame hLevels
  let η' := R.freezing.unaryParameter R.baseProduct η
  let U' := U.freeze R.freezing R.baseProduct
  let X' := X.afterFocusRepair hTag R
  have hSourceForm' := X.frozen_source_form_agreement_row R.freezing R.baseProduct X' U.forms ω hSourceForm hProducts
  have hGood' (b : B) : unaryFamilyParameter η' b ∈ K.good A P :=
    hGood (R.freezing.unaryBaseFreeze R.baseProduct b)
  let L := templateComponentFamily (G := G) hc hv η' K A P hGood' U'.geometry
  let f := unaryCoefficientMap K.coefficient η' (fun b => (hGood' b).1.1.2)
  have hBound (b : B) : vfValue ((f b).val 0) ≤ U'.radius.val :=
    (unaryCoefficientMap_bound K.coefficient η' (fun b => (hGood' b).1.1.2) U'.radius
      (U'.bound _ hCoeffMem) b).2
  obtain ⟨c,hc0,hcDef,hDom,hOldDom⟩ := R.component.exists_named_coefficient_dominating
    h00 hc hv V hV hVS hSV hnt U'.radius U'.named f hBound
  let D := R.refinedSelectedComponent Y c hc0 hcDef hDom
  have hPieces (i : Fin k) : rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))=
      rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η' (P i)) := R.selected_pieces Y i
  refine ⟨{
    geometric := {
    parameter := η'
    family := U'.toUniformProgramFamily
    context := X'
    protectedEq := hPieces
    admissible := hGood'
    fibreComponents := L
    component := D
    coordinate := ?_
    active := ?_
    focus := ?_
    coefficient := ?_
    restrictions := ?_ }
    family := U'
    sourceForm := hSourceForm'
    firstCore := fun b => hCore (R.freezing.unaryBaseFreeze R.baseProduct b) }⟩
  · change R.component.coordinate=K.coordinate.succ
    exact R.coordinate
  · intro p
    let z : Y.coveredBase := Y.coveredFrame.oldPoint ⟨p.val,p.property⟩
    let b := X'.baseMap p
    have hb : unaryFamilyBasePoint z.val=b.val := by
      change unaryFamilyBasePoint (selectedJointPoint π σ p.val)=(X'.baseMap p).val
      rw [selectedJointPoint_base,X'.baseMap_value]
    have h := selectedIndexedFocusGraph_repaired_active_iff hv K Y X.pullback hBRP hBTag hGood
      U.pullback U.toUniformProgramFamily.initial_rows hActiveRows hL R z.val z.property b hb
    have hTags : z.val.2 ∘ Fin.natAdd r=p.val.2 ∘ σ := selectedJointPoint_local π σ p.val
    rw [hTags] at h
    change z.val.2 ∈ R.component.activeTags.carrier ↔ p.val.2 ∘ σ ∈ (L.component b).activeTags.carrier
    rw [L.active b]
    exact h
  · intro p
    let z : Y.coveredBase := Y.coveredFrame.oldPoint ⟨p.val,p.property⟩
    let b := X'.baseMap p
    have hb : unaryFamilyBasePoint z.val=b.val := by
      change unaryFamilyBasePoint (selectedJointPoint π σ p.val)=(X'.baseMap p).val
      rw [selectedJointPoint_base,X'.baseMap_value]
    have h := selectedIndexedFocusGraph_local_focus hv K Y X.pullback hBRP hBTag hGood
      U.pullback U.toUniformProgramFamily.initial_rows hActiveRows hL R z.val z.property b hb (L.component b)
      (hGood' b).1.1.1 (L.active b) (L.focus b)
    have hTags : z.val.2 ∘ Fin.natAdd r=p.val.2 ∘ σ := selectedJointPoint_local π σ p.val
    rw [hTags] at h
    exact (R.refinedSelectedComponent_focus Y c hc0 hcDef hDom ⟨p.val,p.property⟩).trans h
  · intro b
    change vfValue (L.component b).coefficient ≤ vfValue c
    rw [← L.coefficient_map b]
    exact hOldDom b
  · intro i
    rw [← hPieces i]
    exact R.refinedSelectedComponent_restrictions Y h00 hc hκ hs hv c hc0 hcDef hDom i

end DiamondIntegral.Section6
