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
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramRealizations
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleCarrying
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredPreparationTransport
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredSynchronizedTargets
import «section 6».RowMeasuredVFConjugatedPreparation
import «section 6».RowMeasuredVFReindexedPreparation
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
import «section 6».RowMeasuredPermutedCoordinateBundles
import «section 6».RowApertureCoordinateGammaForms
import «section 6».RowArbitraryCoordinateBranches

/-! (Row-form version for Remark 6.20, translated from `MeasuredCoreDimensionInduction`.)
 The lower-dimensional measured induction prepares the retained
core in any actual active coordinate. Every descent, open-level and
protected bundle hypothesis is constructed from the actual component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def MeasuredFormCompatiblePreparationInDimensionRow (S : Set M) (n k : ℕ) : Prop :=
  ∀ r,(A : DefSet (rawMixedSpace (M := M) (n+1) r) S) →
    ProperInvariant S A.carrier → VFDoublyBounded A.carrier → IsRVPullback A.carrier →
    ∀ P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S,
    ∀ hPA : ∀ i,(P i).carrier ⊆ A.carrier,(∀ i,ProperInvariant S (P i).carrier) →
    ∀ ω : RowFormOn A qR,
    (∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) →
    ∃ F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) A F.target F.map P ω

theorem measured_form_compatible_core_of_dimension_induction_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hIH : MeasuredFormCompatiblePreparationInDimensionRow (qR := qR) (G := G) S n k)
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (ω : RowFormOn A qR) (hSafe : D.CoreFormConstantRow ω)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) D.coreRegularizedImage
        (fun i => (E i).coreRegularizedImage) (fun i => (hRestr i).core_image_subset h00) (D.coreGammaFormRow h00 ω),
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) D.coreRegularizedImage T.target T.map
        (fun i => (E i).coreRegularizedImage) (D.coreGammaFormRow h00 ω) := by
  let e := Equiv.swap (Fin.last (n+1)) D.coordinate
  have he : e (Fin.last (n+1))=D.coordinate := Equiv.swap_apply_left _ _
  have hCore := D.coreRegularizedImage_properInvariant h00 hc hκ hs hv
  have hGeometry := D.coreGammaForm_levels_geometry_row h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  have hCoreLevels := fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen
  obtain ⟨η,hη,hηLevels⟩ := (D.coreGammaForm_coordinate_constant_row h00 ω hSafe).exists_coordinate_descent_row
    h00 hc linear hκ hs hv hsmall hΓ hCore e he hCoreLevels
  obtain ⟨F,hF⟩ := hIH _ (coordinateProjection D.coreRegularizedImage e)
    (coordinateProjection_properInvariant _ e hCore)
    (coordinateProjection_doublyBounded _ e D.coreRegularizedImage_doublyBounded)
    (vfDropLast_image_rvPullback (reindexedVFSet_rvPullback _ e (D.coreRegularizedImage_rvPullback h00 hARV)))
    (fun i => coordinateProjection (E i).coreRegularizedImage e)
    (fun i => coordinateProjection_subset ((hRestr i).core_image_subset h00) e)
    (fun i => coordinateProjection_properInvariant _ e ((E i).coreRegularizedImage_properInvariant h00 hc hκ hs hv))
    η hηLevels
  apply measured_form_compatible_coordinate_bundle_of_projected_preparation_row h00 hc hκ hs hv
    D.coreRegularizedImage hCore D.coreRegularizedImage_doublyBounded _ (fun i => (hRestr i).core_image_subset h00)
    e (Fin.castAdd (1+r) D.coordinate) _ _ (D.coreGammaFormRow h00 ω) η hη F hF
  · exact reindexed_coordinate_bundle_of_replacement _ e D.coordinate he _
      (D.coreRegularizedImage_leading_tag_row h00) (D.coreRegularizedImage_replace_row h00)
  · intro i
    have hj : e (Fin.last (n+1))=(E i).coordinate := he.trans (hRestr i).coordinate.symm
    have h := reindexed_coordinate_bundle_of_replacement _ e (E i).coordinate hj _
      ((E i).coreRegularizedImage_leading_tag_row h00) ((E i).coreRegularizedImage_replace_row h00)
    simpa only [(hRestr i).coordinate] using h

end DiamondIntegral.Section6
