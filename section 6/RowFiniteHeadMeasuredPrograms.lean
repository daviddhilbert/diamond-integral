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
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormFreezing
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowHeadGammaFormMaps
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
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
import «section 6».RowHeadGammaFormTemplates
import «section 6».CoordinateProgramData
import «section 6».RowFiniteMeasuredCentripetalPrograms

/-! (Row-form version for Remark 6.20, translated from `FiniteHeadMeasuredPrograms`.)
 Actual measured preparations on the head fibres admit finitely
many whole original-base programs whose terminal tests also retain the
Gamma form. This is the finite selection step; it does not assume that
their subsequent higher-dimensional fusion has been completed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_head_measured_programs_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hARV : IsRVPullback A.carrier)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (ω : RowFormOn A qR)
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparationRow (G := G)
      ((headFibreTemplate A).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPA i) a) (headGammaFormMapRow ω a),
        SynchronizedCentripetalChain (G := G) (Fin k)
          ((headFibreTemplate A).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S 1 (n+1) r s,
      ∀ a : VF M,∃ i,(fun _ : Fin 1 => a.val) ∈ (T i).2.measuredGoodRow
        (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) := by
  let X := (rawVFSpace (M := M) 1).domain
  have hX : S.Definable LRV X := (rawVFSpace (M := M) 1).definable_domain S
  have hLocalRaw (z : Fin 1 → M) (hz : z ∈ X) :
      ∃ s,∃ B : DefSet (rawMixedSpace (M := M) (n+1) s) (S ∪ Set.range z),
      ∃ f : Map ((headFibreTemplate A).fibre z) B,
      ∃ h : SynchronizedCentripetalChain (G := G) (Fin k) ((headFibreTemplate A).fibre z) B f
          (fun i => (headFibreTemplate (P i)).fibre z),
        IsRVPullback ((headFibreTemplate A).fibre z).carrier ∧
          (∀ i,IsRVPullback (f.restrict (h.atPiece i).source_subset).image.carrier) ∧
          ∃ θ : RowFormOn ((headFibreTemplate A).fibre z) qR,
            {w | Sum.elim z w ∈ (headGammaFormTemplateRow ω).graph}=
              (rawMixedSpace (n+1) r).relation (rawRVSpace (M := M) qR) θ.graph ∧
              ∀ t u : (headFibreTemplate A).fibre z,(f t).val.2=(f u).val.2 → (θ t).val=(θ u).val := by
    obtain ⟨a,rfl⟩ := (raw_unary_vf_parameter_iff z).mp hz
    obtain ⟨F,hF⟩ := hLocal a
    refine ⟨F.arity,F.target,F.map,hF,headFibreTemplate_rvPullback A hARV a,
      (fun i => (F.pieces i).2),headGammaFormMapRow ω a,headGammaFormTemplate_section_row ω a,?_⟩
    intro t u he
    have h := F.constant (F.map t).val (F.map t).property (F.map u).val (F.map u).property he
    rw [rowFormExtension_at F.form (F.map t),rowFormExtension_at F.form (F.map u)] at h
    exact (F.transportRow t).symm.trans (h.trans (F.transportRow u))
  obtain ⟨l,T,hCover⟩ := exists_finite_measured_centripetal_programs_row h00 hc linear hκ hs hv hsmall hΓ
    X hX (headFibreTemplate A) (fun i => headFibreTemplate (P i)) (headGammaFormTemplateRow ω) hLocalRaw
  exact ⟨l,T,fun a => hCover (fun _ => a.val) ⟨(fun _ => a),rfl⟩⟩

end DiamondIntegral.Section6
