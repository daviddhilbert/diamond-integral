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
import «section 6».RowVFReindexedGammaForms
import «section 6».RowFormCompatibleVFReindexing
import «section 6».RowMeasuredPreparationTransport

/-! (Row-form version for Remark 6.20, translated from `MeasuredVFReindexedPreparation`.)
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

theorem MeasuredCoordinatePreparationRow.refine_vf_coordinates_form_compatible_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    {ω : RowFormOn A qR}
    (F : MeasuredCoordinatePreparationRow (G := G) A P hPA ω)
    (hF : FormCompatibleSynchronizedChainRow (G := G) (Fin k) A F.target F.map P ω)
    {e : Fin (n+1) ≃ Fin (n+1)} (X : VFReindexRefinementFrame A e) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) X.data.base (fun i => X.selectedPiece (P i))
        (fun i => X.selectedPiece_subset (P i)) (ω.comp X.oldMapRow),
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) X.data.base T.target T.map
        (fun i => X.selectedPiece (P i)) (ω.comp X.oldMapRow) := by
  obtain ⟨K,hK⟩ := hF.vf_reindexed_lift_exists h00 hc hκ hs hv X
  have hPrepared (i) : IsRVPullback (K.map.restrict (X.selectedPiece_subset (P i))).image.carrier := by
    rw [K.partition_image h00 (F.special.bijective h00).injective i (hPA i)]
    apply labelRefinement_pullback (reindexedVFSet (F.map.restrict (hPA i)).image e)
      (K.target.data.selectedPiece (reindexedVFSet (F.map.restrict (hPA i)).image e)) K.target.data.labels
      (K.target.data.selectedPiece_fibres _ ?_) (reindexedVFSet_rvPullback _ e (F.pieces i).2)
    intro q hq
    apply (mem_reindexedVFSet F.target e q).mpr
    obtain ⟨p,hp⟩ := (mem_reindexedVFSet (F.map.restrict (hPA i)).image e q).mp hq
    exact hp ▸ (F.map.restrict (hPA i) p).property
  refine ⟨{
    arity := K.target.data.arity
    target := K.target.data.base
    map := K.map
    special := hK.toSynchronizedRow.toChain.toSpecial
    proper := K.target.data.proper
    doublyBounded := K.target.data.doublyBounded
    prepared := K.target.data.pullback (reindexedVFSet_rvPullback F.target e F.prepared)
    tagged := labelRefinement_tagged (reindexedVFSet F.target e) K.target.data.base K.target.data.labels
      K.target.data.fibres (reindexedVFSet_tagged F.target e F.tagged)
    form := F.form.comp K.target.oldMapRow
    transportRow := K.gamma_form_transport_row ω F.form F.transportRow
    constant := K.target.gamma_form_constant_row F.form F.constant
    pieces := fun i => ⟨(hK.toSynchronizedRow.atPiece i).literal_restriction h00 (X.selectedPiece_subset (P i)),hPrepared i⟩ },hK⟩

end DiamondIntegral.Section6
