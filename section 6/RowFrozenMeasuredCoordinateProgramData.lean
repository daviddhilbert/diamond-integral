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
import «section 6».RowMeasuredProgramChoicePartitions
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
import «section 6».RowMeasuredProgramGeometricData
import «section 6».RowMeasuredFrozenUnaryRVTemplatePreparation
import «section 6».FrozenCoordinateProgramData
import «section 6».FrozenParameterPrograms

/-! (Row-form version for Remark 6.20, translated from `FrozenMeasuredCoordinateProgramData`.)
 Construct the complete finite-program data, freeze and prepare its
whole membership relation, and lift that unary preparation to the actual
ambient. Formula choices and every selected program row are retained,
with the original ambient and protected source sets unchanged by freezing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r n k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramTemplate.substitute_measuredFormGood_row
    {p q d a b k : ℕ}
    (T : CentripetalProgramTemplate (M := M) S p d a b)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p d a)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p d a)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p d a) :
    (T.substitute h).measuredFormGoodRow (A.substitute h) (fun i => (P i).substitute h) (W.substitute h)=
      h.value ⁻¹' T.measuredFormGoodRow A P W := by
  unfold CentripetalProgramTemplate.measuredFormGoodRow
  rw [T.substitute_measuredGood_row h A P W,T.substitute_coreFormGood_row h A W]
  rfl

structure FrozenMeasuredCoordinateProgramDataRow
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (X : UnaryPreparationContext A (0 : Fin (n+2)))
    (P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S)
    (ω : RowFormOn X.source qR) where
  programs : FiniteMeasuredCoordinateProgramDataRow X.source P ω
  unary : MeasuredUnaryRVTemplateFreezeCertificateRow (G := G) A C hCA X P programs.completeData ω

namespace FrozenMeasuredCoordinateProgramDataRow
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : RowFormOn X.source qR}

def substitution (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω) :
    DefinableParameterSubstitution (M := M) S 1 1 :=
  FMT.freezingParameterSubstitution F.unary.freezing.balls F.unary.freezing.centers F.unary.freezing.separated
    F.unary.freezing.balls_definable F.unary.freezing.centers_definable

theorem sources_preserved (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω) :
    ((headFibreTemplate X.source).substitute F.substitution).uncurry=X.source ∧
      ∀ i,((headFibreTemplate (P i)).substitute F.substitution).uncurry=P i :=
  ⟨FMT.uncurry_substituted_head_source _ _ _ _ _ X.source F.unary.ambientProduct,
    fun i => FMT.uncurry_substituted_head_source _ _ _ _ _ (P i) (F.unary.protectedProducts i)⟩

theorem choices_constant (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω)
    (p z : A) (he : (F.unary.map p).val.2=(F.unary.map z).val.2) :
    ∀ i,F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i ↔
      F.substitution.value (fun _ => (z.val.1 0).val) ∈ F.programs.choices i := by
  exact choices_eq_of_measured_program_data_eq_row h00 F.programs.programs (headFibreTemplate X.source)
    (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) F.programs.choices F.programs.choices_definable _ _ (F.unary.data p z he)

theorem selected_rows_constant (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω)
    (p z : A) (he : (F.unary.map p).val.2=(F.unary.map z).val.2)
    (i : Fin F.programs.count) (hi : F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i) :
    ∀ D ∈ (F.programs.programs i).2.measuredRVTraceRow (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)) (headGammaFormTemplateRow ω),
      (D.2.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier=
        (D.2.fibre (F.substitution.value (fun _ => (z.val.1 0).val))).carrier := by
  exact selected_trace_rows_eq_of_measured_program_data_eq_row h00 F.programs.programs (headFibreTemplate X.source)
    (fun j => headFibreTemplate (P j)) (headGammaFormTemplateRow ω) F.programs.choices F.programs.choices_definable _ _ (F.unary.data p z he) i hi

theorem substituted_measured_good_row
    (F : FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω) (a : Fin 1 → M)
    (i : Fin F.programs.count) (hi : F.substitution.value a ∈ F.programs.choices i) :
    a ∈ ((F.programs.programs i).2.substitute F.substitution).measuredFormGoodRow
      ((headFibreTemplate X.source).substitute F.substitution)
      (fun j => (headFibreTemplate (P j)).substitute F.substitution) ((headGammaFormTemplateRow ω).substitute F.substitution) := by
  rw [(F.programs.programs i).2.substitute_measuredFormGood_row]
  exact (F.programs.choices_subset i hi).2

end FrozenMeasuredCoordinateProgramDataRow

theorem exists_frozen_measured_coordinate_program_data_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hW : ∀ a ∈ W,iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (X : UnaryPreparationContext A (0 : Fin (n+2)))
    (P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : RowFormOn X.source qR)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ X.source.carrier ∧ rowFormExtension ω (x,u)=γ})
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparationRow (G := G)
      ((headFibreTemplate X.source).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPX i) a) (headGammaFormMapRow ω a),
        FormCompatibleSynchronizedChainRow (G := G) (Fin l)
          ((headFibreTemplate X.source).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMapRow ω a)) :
    Nonempty (FrozenMeasuredCoordinateProgramDataRow (G := G) A C hCA X P ω) := by
  obtain ⟨F⟩ := exists_finite_measured_coordinate_program_data_row h00 hc linear hκ hs hv hsmall hΓ
    X.source X.proper X.doublyBounded X.pullback P hPX hP ω hLocal
  obtain ⟨R⟩ := measured_frozen_unary_rv_template_preparation_row h00 hc linear hκ hs hv W hsmall hΓ hW hWS hSW hnt
    A hA hAD hARV hTag C hCA hC X P hPX hP F.completeData ω hLevels
  exact ⟨⟨F,R⟩⟩

end DiamondIntegral.Section6
