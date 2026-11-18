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
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowMeasuredCentripetalProgramTemplates
import Section3.SmallFiniteParameters

/-! (Row-form version for Remark 6.20, translated from `FiniteMeasuredCentripetalPrograms`.)
 Genuine compactness gives finitely many complete measured programs
for a definable family of locally prepared pullback fibres. Their
lengths and output RV arities consequently have one finite bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_measured_centripetal_programs_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (X : Set (Fin p → M)) (hX : S.Definable LRV X)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplateRow (qR := qR) (M := M) S p n r)
    (hLocal : ∀ a ∈ X,∃ s,∃ B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a),
      ∃ f : Map (A.fibre a) B,
      ∃ h : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a),
        IsRVPullback (A.fibre a).carrier ∧
          (∀ i,IsRVPullback (f.restrict (h.atPiece i).source_subset).image.carrier) ∧
          ∃ ω : RowFormOn (A.fibre a) qR,
            {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation (rawRVSpace (M := M) qR) ω.graph ∧
            ∀ t u : A.fibre a,(f t).val.2=(f u).val.2 → (ω t).val=(ω u).val) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s,
      ∀ a ∈ X,∃ i,a ∈ (T i).2.measuredGoodRow A P W := by
  let C := Set.range (fun T : Σ s,CentripetalProgramTemplate (M := M) S p n r s => T.2.measuredGoodRow A P W)
  have hC : ∀ c ∈ C,S.Definable LRV c := by
    rintro c ⟨T,rfl⟩
    exact T.2.measuredGood_definable_row A P W
  have hCover (a) (ha : a ∈ X) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨s,B,f,h,hARV,hPrepared,ω,hW,hConst⟩ := hLocal a ha
    have hsmallA := small_union_range hκ.le S hsmall a
    have hGammaA : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M) :=
      hΓ.mono Set.subset_union_left (Set.Subset.rfl)
    obtain ⟨T,hT,hGraph⟩ := exists_promoted_measured_centripetal_program_row h00 hc linear hκ hs hv
      A P W a hsmallA hGammaA h hARV (fun i => (h.atPiece i).source_subset) hPrepared ω hW hConst
    exact ⟨T.measuredGoodRow A P W,⟨⟨s,T⟩,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall X hX C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).2.measuredGoodRow A P W=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => chooseT (e.symm i),?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).2.measuredGoodRow A P W
  rw [e.symm_apply_apply,hT]
  exact hac

end DiamondIntegral.Section6
