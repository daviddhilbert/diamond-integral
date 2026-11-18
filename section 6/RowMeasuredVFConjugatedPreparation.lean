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
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».VFConjugatedPreparation

/-! (Row-form version for Remark 6.20, translated from `MeasuredVFConjugatedPreparation`.)
 Preparation in permuted VF coordinates returns to literal original
coordinates through actual permitted operations. The original Gamma
map and all protected images are recovered exactly. -/

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

theorem measured_preparation_conjugate_vf_coordinates_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (e : Fin (n+1) ≃ Fin (n+1)) (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (ω : RowFormOn A qR)
    (F : MeasuredCoordinatePreparationRow (G := G) (reindexedVFSet A e)
      (fun i => reindexedVFSet (P i) e) (fun i q hq =>
        (mem_reindexedVFSet A e q).mpr (hPA i ((mem_reindexedVFSet (P i) e q).mp hq))) (reindexedGammaFormRow ω e))
    (hF : FormCompatibleSynchronizedChainRow (G := G) (Fin k) (reindexedVFSet A e) F.target F.map
      (fun i => reindexedVFSet (P i) e) (reindexedGammaFormRow ω e)) :
    ∃ T : MeasuredCoordinatePreparationRow (G := G) A P hPA ω,
      FormCompatibleSynchronizedChainRow (G := G) (Fin k) A T.target T.map P ω := by
  let X := VFReindexRefinementFrame.conjugation A e hA hD
  obtain ⟨K,hK⟩ := F.refine_vf_coordinates_form_compatible_row h00 hc hκ hs hv hF X
  have hForm (p : A) : (((reindexedGammaFormRow ω e).comp X.oldMapRow) p).val=(ω p).val := by
    have hPoint : reindexVFInverseMapRow A e (X.oldMapRow p)=p := by
      apply Subtype.ext
      change reindexVFPoint e.symm (reindexVFPoint e (p.val.1,p.val.2 ∘ id))=p.val
      rw [Function.comp_id,reindexVFPoint_inverse]
      rfl
    change (ω (reindexVFInverseMapRow A e (X.oldMapRow p))).val=(ω p).val
    rw [hPoint]
  let T : MeasuredCoordinatePreparationRow (G := G) A P hPA ω :=
    (K.changeFormRow hForm).changePieces (fun i => VFReindexRefinementFrame.conjugation_piece A e hA hD (P i) (hPA i))
  exact ⟨T,(hK.changeFormRow hForm).changePieces (fun i =>
    VFReindexRefinementFrame.conjugation_piece A e hA hD (P i) (hPA i))⟩

end DiamondIntegral.Section6
