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
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredFormCompatibleTargets
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
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
import «section 6».RowFormCompatibleRVRefinement
import «section 6».RowMeasuredPreparationTransport

/-! (Row-form version for Remark 6.20, translated from `MeasuredRVRefinementPreparation`.)
 Actual measured preparation lifts through a refinement of RV labels,
retaining its component form condition, exact Gamma values, target
constancy, tagged geometry and every literal protected image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem MeasuredCoordinatePreparationRow.refine_rv_labels_form_compatible_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    {ω : RowFormOn A qR}
    (F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω)
    (hF : FormCompatibleSynchronizedChainRow (G := G) (Fin k) A F.target F.map P ω)
    (X : RVRefinementFrame A) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) X.base (fun i => X.selectedPiece (P i))
        (fun i => X.selectedPiece_subset (P i)) (ω.comp X.oldMap),
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) X.base T.target T.map
        (fun i => X.selectedPiece (P i)) (ω.comp X.oldMap) := by
  obtain ⟨K,hK⟩ := hF.rv_refinement_lift_exists h00 hc hκ hs hv X
  have hPrepared (i) : IsRVPullback (K.map.restrict (X.selectedPiece_subset (P i))).image.carrier := by
    rw [K.partition_image h00 (F.special.bijective h00).injective i (hPA i)]
    apply labelRefinement_pullback (F.map.restrict (hPA i)).image
      (K.target.selectedPiece (F.map.restrict (hPA i)).image) K.target.labels
      (K.target.selectedPiece_fibres _ ?_) (F.pieces i).2
    rintro q ⟨p,hp⟩
    exact hp ▸ (F.map.restrict (hPA i) p).property
  refine ⟨{
    arity := K.target.arity
    target := K.target.base
    map := K.map
    special := hK.toSynchronizedRow.toChain.toSpecial
    proper := K.target.proper
    doublyBounded := K.target.doublyBounded
    prepared := K.target.pullback F.prepared
    tagged := labelRefinement_tagged F.target K.target.base K.target.labels K.target.fibres F.tagged
    form := F.form.comp K.target.oldMap
    transportRow := K.gamma_form_transport_row ω F.form F.transportRow
    constant := K.target.gamma_form_constant_row F.form F.constant
    pieces := fun i => ⟨(hK.toSynchronizedRow.atPiece i).literal_restriction h00 (X.selectedPiece_subset (P i)),hPrepared i⟩ },hK⟩

end DiamondIntegral.Section6
