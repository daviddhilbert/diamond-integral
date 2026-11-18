import «section 6».RowBinaryMeasuredRootTermination
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
import «section 6».RowMeasuredVFReindexedPreparation
import «section 6».RowPreparedCoverGammaForms
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
import «section 6».RowApertureCoordinateGammaForms
import «section 6».RowArbitraryCoordinateBranches

/-! (Row-form version for Remark 6.20, translated from `VariableApertureGammaForms`.)
 The variable old aperture in a genuine fusion step has its own
semantic form condition. This controls the released annulus even though
it is outside the smaller new core. No constant old coefficient or
finite set of Gamma values is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def VariableCoreFormConstantRow (D : CentripetalData (G := G) A)
    (ρ : (Fin r → RVInfinity M) → Gamma M)
    (ω : RowFormOn A qR) : Prop :=
  ∀ p q : A,p.val.2 ∈ D.activeTags.carrier → q.val.2 ∈ D.activeTags.carrier →
    (ρ p.val.2).val < vfValue (p.val.1 D.coordinate-D.extendedFocus p.val) →
    (ρ q.val.2).val < vfValue (q.val.1 D.coordinate-D.extendedFocus q.val) →
    (∀ i,i ≠ D.coordinate → p.val.1 i=q.val.1 i) → p.val.2=q.val.2 → (ω p).val=(ω q).val

def variableReleasedGammaFormRow (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR) :
    RowFormOn (D.variableReleasedImage U) qR :=
  (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective_row D h00))).comp
    (Map.inclusion (fun _ hp => hp.1))

theorem variableReleasedGammaForm_at_row (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) (h00 : M ⊨ Axioms.ACVF00)
    (ω : RowFormOn A qR)
    (q : D.variableReleasedImage U) (p : A) (he : regularize (D.point p.val)=q.val) :
    rowFormExtension (D.variableReleasedGammaFormRow U h00 ω) q.val=(ω p).val := by
  rw [rowFormExtension_at]
  change (ω ((centripetalStepMap D).inverse _ ⟨q.val,q.property.1⟩)).val=(ω p).val
  have hf : centripetalStepMap D p=⟨q.val,q.property.1⟩ := Subtype.ext he
  rw [← hf,Map.inverse_apply]

theorem variableReleasedGammaForm_coordinate_constant_row (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) (h00 : M ⊨ Axioms.ACVF00)
    (ρ : (Fin r → RVInfinity M) → Gamma M) (H : VariableApertureReleaseData D U ρ)
    (ω : RowFormOn A qR) (hSafe : D.VariableCoreFormConstantRow ρ ω) :
    CoordinateGammaConstantRow D.coordinate (D.variableReleasedGammaFormRow U h00 ω) := by
  intro q q' hOther hTags
  obtain ⟨p,hp,hpU,he⟩ := (D.mem_variableReleasedImage U q.val).mp q.property
  obtain ⟨p',hp',hpU',he'⟩ := (D.mem_variableReleasedImage U q'.val).mp q'.property
  let x : A := ⟨p,hp⟩
  let y : A := ⟨p',hp'⟩
  have hx : (centripetalStepMap D x).val=q.val := he
  have hy : (centripetalStepMap D y).val=q'.val := he'
  have hOldTags : p.2=p'.2 := (D.coordinate_step_same_labels_row h00 x y (by
    change (centripetalStepMap D x).val.2=(centripetalStepMap D y).val.2
    rw [hx,hy]
    exact hTags)).1
  have hOldOther (i) (hi : i ≠ D.coordinate) : p.1 i=p'.1 i := by
    rw [← D.coordinate_step_other_row x i hi,← D.coordinate_step_other_row y i hi,hx,hy]
    exact hOther i hi
  obtain ⟨hAct,hOld,hNew⟩ := (H.labels p hp).mp hpU
  obtain ⟨hAct',hOld',hNew'⟩ := (H.labels p' hp').mp hpU'
  have h := hSafe x y hAct hAct' hOld hOld' hOldOther hOldTags
  rw [← rowFormExtension_at _ q,← rowFormExtension_at _ q']
  rw [D.variableReleasedGammaForm_at_row U h00 ω q x he,D.variableReleasedGammaForm_at_row U h00 ω q' y he']
  exact h

theorem variableReleasedGammaForm_levels_geometry_row (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ rowFormExtension ω (x,u)=γ}) :
    ∀ γ,ProperInvariantGeometry {q | q ∈ (D.variableReleasedImage U).carrier ∧
      rowFormExtension (D.variableReleasedGammaFormRow U h00 ω) q=γ} := by
  have hStep : SpecialCovariantChain (G := G) A (regularizeMap D.map.image).image (centripetalStepMap D) :=
    .comp (.centripetal A D) (.regularize D.map.image
      (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded)
  have hGeometry := hStep.gamma_levels_proper_geometry_row h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  intro γ
  exact gammaFormRestriction_level_geometry_row (A := (regularizeMap D.map.image).image)
    (C := D.variableReleasedImage U) (fun _ hp => hp.1)
    (D.variableReleasedImage_properInvariant h00 hc hκ hs hv U).geometry
    (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective_row D h00))) γ (hGeometry γ)

end DiamondIntegral.Section6.CentripetalData
