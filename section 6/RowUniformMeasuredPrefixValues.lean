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
import «section 6».RowFormCompatibleProgramLoci
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaCoreComponentSemantics
import «section 6».RowGammaCoreParameterLoci
import «section 6».RowGammaCoreParameterSemantics
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormRVTraceBounds
import «section 6».RowGammaFormRVTraces
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaRVTraceValues
import «section 6».RowGammaTransitionImages
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramPrefixLoci
import «section 6».RowMeasuredProgramRVTraces
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
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
import «section 6».RowUniformMeasuredProgramFamilies
import «section 6».RowUniformMeasuredProgramPrefixes
import «section 6».CodeGraphValueUniqueness

/-! (Row-form version for Remark 6.20, translated from `UniformMeasuredPrefixValues`.)
 The remaining family agrees with inverse transportRow through every
actual realization of the prefix. Its canonical choice of a realization
does not impose an additional compatibility assumption on global fusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformMeasuredProgramFamilyRow
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t v k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

/-- Row forms whose marked graphs have the same code relation agree at equal points. -/
theorem rowForm_values_eq_of_code_graph_eq_row {T U : Set M}
    {A : DefSet (rawMixedSpace (M := M) n t) T} {A' : DefSet (rawMixedSpace (M := M) n t) U}
    (ρ : RowFormOn A qR) (η : RowFormOn A' qR)
    (hGraph : (rawMixedSpace n t).relation (rawRVSpace (M := M) qR) ρ.graph =
      (rawMixedSpace n t).relation (rawRVSpace (M := M) qR) η.graph)
    (p : A) (q : A') (hPoint : p.val = q.val) : (ρ p).val = (η q).val := by
  have key : ∀ {T U : Set M} {A : DefSet (rawMixedSpace (M := M) n t) T}
      {A' : DefSet (rawMixedSpace (M := M) n t) U} (ρ : RowFormOn A qR) (η : RowFormOn A' qR),
      (rawMixedSpace n t).relation (rawRVSpace (M := M) qR) ρ.graph =
        (rawMixedSpace n t).relation (rawRVSpace (M := M) qR) η.graph →
      ∀ (p : A) (q : A'), p.val = q.val → ∀ v ∈ (ρ p).val, v ∈ (η q).val := by
    intro T U A A' ρ η hG p q hpq v hv
    obtain ⟨x, hx⟩ := (rawMixedSpace (M := M) n t).onto p.val
    obtain ⟨y, hy⟩ := (rawRVSpace (M := M) qR).onto v
    have hMem := ((rawMixedSpace (M := M) n t).relation_decode (rawRVSpace (M := M) qR) ρ.graph x y).mpr
      ⟨p, hx.symm, Or.inl (by rw [hy]; exact hv)⟩
    rw [hG] at hMem
    obtain ⟨a, ha, hva⟩ :=
      ((rawMixedSpace (M := M) n t).relation_decode (rawRVSpace (M := M) qR) η.graph x y).mp hMem
    have haq : a = q := Subtype.ext (ha.trans (hx.trans hpq))
    subst haq
    rcases hva with h | h
    · rw [hy] at h
      exact h
    · rw [hy] at h
      exact absurd (h ▸ hv) (RowFormOn.rowMarker_not_mem ρ p)
  ext v
  exact ⟨key ρ η hGraph p q hPoint v, key η ρ hGraph.symm q p hPoint.symm v⟩

theorem afterPrefix_value_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {F : CentripetalProgramTemplate (M := M) S 1 n s t}
    {H : CentripetalProgramTemplate (M := M) S 1 n t v}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {W : GammaFormParameterTemplateRow (qR := qR) (M := M) S 1 n s}
    (U : UniformMeasuredProgramFamilyRow (G := G) η (F.comp H) A P W) (b : B)
    {Z : DefSet (rawMixedSpace (M := M) n t) (S ∪ Set.range (unaryFamilyParameter η b))}
    (f : Map (A.fibre (unaryFamilyParameter η b)) Z) (hf : Function.Bijective f)
    (hF : {z | Sum.elim (unaryFamilyParameter η b) z ∈ (F.transition A).graph}=
      (rawMixedSpace n s).relation (rawMixedSpace n t) f.graph)
    (x : A.fibre (unaryFamilyParameter η b)) (y : (F.target A).fibre (unaryFamilyParameter η b))
    (hPoint : y.val=(f x).val) :
    ((U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms b y).val=(U.forms b x).val := by
  let V := U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ
  let ζ := (U.forms b).comp (f.inverse hf)
  have hGraph := gammaTransitionImage_at_row (unaryFamilyParameter η b) (F.transition A).graph W.graph
    f hf (U.forms b) hF (U.graphs b)
  have hSame := rowForm_values_eq_of_code_graph_eq_row (V.forms b) ζ ((V.graphs b).symm.trans hGraph) y (f x) hPoint
  change (V.forms b y).val=(U.forms b (f.inverse hf (f x))).val at hSame
  rw [Map.inverse_apply] at hSame
  exact hSame

end DiamondIntegral.Section6.UniformMeasuredProgramFamilyRow
