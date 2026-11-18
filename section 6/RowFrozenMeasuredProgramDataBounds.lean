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
import «section 6».RowFiniteFormCompatiblePrograms
import «section 6».RowFiniteHeadFormCompatiblePrograms
import «section 6».RowFiniteHeadMeasuredPrograms
import «section 6».RowFiniteMeasuredCentripetalPrograms
import «section 6».RowFormCompatibleFocusSteps
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleSynchronizedChains
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
import «section 6».RowHeadGammaFormMaps
import «section 6».RowHeadGammaFormTemplates
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredChoiceProgramRVData
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredCoordinateProgramData
import «section 6».RowMeasuredFrozenUnaryRVDataPreparation
import «section 6».RowMeasuredFrozenUnaryRVTemplatePreparation
import «section 6».RowMeasuredProgramChoicePartitions
import «section 6».RowMeasuredProgramGeometricData
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredProtectedUnaryDataFreezing
import «section 6».RowMeasuredUnaryContextSteps
import «section 6».RowMeasuredUnaryValueContextPreparation
import «section 6».RowMeasuredUnaryValueContextStep
import «section 6».RowPreparedFormCompatiblePrograms
import «section 6».RowPromotedFormCompatiblePrograms
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
import «section 6».RowFrozenMeasuredCoordinateProgramData
import «section 6».DefinableRVRowDescent
import «section 6».UnaryRVRowDefinability
import «section 6».PreparedRVObjects

/-! (Row-form version for Remark 6.20, translated from `FrozenMeasuredProgramDataBounds`.)
 The complete frozen finite-program data have an actual uniform
original-base named bound after unary preparation. The bounded RV base,
definable row descent and separate row bounds are constructed from the
preparation certificate; no initial VF-indexed uniform bound is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r n k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : RowFormOn X.source qR}

theorem FrozenMeasuredCoordinateProgramDataRow.uniform_named_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ X.source.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ p : A,∀ u ∈ (F.programs.completeData.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier,
        ∀ i,(δ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ δ.val := by
  let q := (pureRVTagQuotient F.unary.target).comp F.unary.map
  have hq : Function.Surjective q := (pureRVTagQuotient_surjective F.unary.target).comp
    (F.unary.chain.toChain.toSpecial.bijective h00).surjective
  have hBase : RVValueDoublyBounded (pureRVTagDomain F.unary.target).carrier :=
    preparedRVObject_domain_doublyBounded F.unary.target F.unary.tagged F.unary.proper.rvBounded
  let V := F.programs.completeData.substitute F.substitution
  let R := unaryRVRowRelation (r := r) V
  have hR := unaryRVRowRelation_definable (r := r) V
  have hCarrier (p : A) : {u | R p.val u}=
      (F.programs.completeData.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier := by
    ext u
    rfl
  have hSame (p z : A) (he : (q p).val=(q z).val) : ∀ u,R p.val u ↔ R z.val u := by
    have hLabels : (F.unary.map p).val.2=(F.unary.map z).val.2 := he
    have hData : (F.programs.completeData.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier=
        (F.programs.completeData.fibre (F.substitution.value (fun _ => (z.val.1 0).val))).carrier := F.unary.data p z hLabels
    intro u
    exact (Set.ext_iff.mp (hCarrier p) u).trans
      ((Set.ext_iff.mp hData u).trans (Set.ext_iff.mp (hCarrier z) u).symm)
  have hRows (p : A) : RVValueDoublyBounded {u | R p.val u} := by
    rw [hCarrier]
    exact F.programs.completeData_rows_bounded h00 hc hκ hs hv linear hsmall hΓ hLevels _
  obtain ⟨δ,hδ,hBound⟩ := definable_rv_row_descent_named_bound hc h00 linear hκ.le hs hsmall hΓ q hq hBase R hR hSame hRows
  refine ⟨δ,hδ,?_⟩
  intro p u hu i
  exact hBound p u ((Set.ext_iff.mp (hCarrier p) u).mpr hu) i

end DiamondIntegral.Section6
