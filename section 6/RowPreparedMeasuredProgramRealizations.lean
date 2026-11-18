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
import «section 6».RowExactGammaTransport
import «section 6».RowFiniteMeasuredCentripetalPrograms
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedCoverGammaForms
import «section 6».RowPreparedVariableRelease
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
import «section 6».RowMeasuredCentripetalProgramRealizations
import «section 6».RowMeasuredSynchronizedTargets

/-! (Row-form version for Remark 6.20, translated from `PreparedMeasuredProgramRealizations`.)
 Measured-admissible actual programs produce full positive-degree
measured preparation witnesses, with the entire synchronized permitted
chain and every literal protected image. Only one final regularization
is added to the specified program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramTemplate.exists_prepared_measured_realization_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p (n+1) r s)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p (n+1) r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p (n+1) r) (a : Fin p → M)
    (ha : a ∈ T.measuredGoodRow A P W) (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier) (hARV : IsRVPullback (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier)
    (ω : RowFormOn (A.fibre a) qR)
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace (n+1) r).relation (rawRVSpace (M := M) qR) ω.graph) :
    ∃ U : MeasuredCoordinatePreparationRow (G := G) (A.fibre a) (fun i => (P i).fibre a) hPA ω,
      SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) U.target U.map (fun i => (P i).fibre a) := by
  obtain ⟨F⟩ := T.exists_realization h00 hc hκ hs hv A P a ha.1.1 hA hAD hPA hP
  let R : PreparedSynchronizedFamily (G := G) (A.fibre a) (fun i => (P i).fibre a) hPA := {
    arity := s
    target := (T.target A).fibre a
    map := F.map
    chain := F.chain
    proper := F.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
    doublyBounded := F.chain.toChain.toSpecial.target_vfDoublyBounded hAD
    pullback := F.chain.toChain.target_rvPullback h00 hARV
    prepared := (F.prepared_iff ha.1.1 hPA).mp ha.1 }
  exact R.measured_target_row h00 hc hκ hs hv ω
    ((gammaTransitionConstantParameterLocus_iff_row a _ _ F.map ω F.graph hW).mp ha.2)

end DiamondIntegral.Section6
