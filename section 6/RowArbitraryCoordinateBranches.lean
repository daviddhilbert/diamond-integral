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
import «section 6».PermutedCoordinateBundles
import «section 6».SynchronizedApertureBranches
import «section 6».RowPreparedVariableRelease

/-! (Row-form version for Remark 6.20, translated from `ArbitraryCoordinateBranches`.)
 The retained core and the variable-aperture annulus admit the
dimension-induction preparation in the actual active coordinate.
All projections and restrictions are over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
namespace CentripetalData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem coreRegularizedImage_leading_tag_row (h00 : M ⊨ Axioms.ACVF00)
    (D : CentripetalData (G := G) A) (q : Mixed M (n+1) ((n+1)+(1+r)))
    (hq : q ∈ D.coreRegularizedImage.carrier) :
    rv M (q.1 D.coordinate)=q.2 (Fin.castAdd (1+r) D.coordinate) := by
  obtain ⟨a,ha,hCore,rfl⟩ := (D.mem_coreRegularizedImage h00 q).mp hq
  simp only [regularize,Fin.append_left]
  rfl

theorem coreRegularizedImage_replace_row (h00 : M ⊨ Axioms.ACVF00)
    (D : CentripetalData (G := G) A) (q : Mixed M (n+1) ((n+1)+(1+r)))
    (hq : q ∈ D.coreRegularizedImage.carrier) (d : VF M)
    (hrv : rv M d=rv M (q.1 D.coordinate)) :
    (Function.update q.1 D.coordinate d,q.2) ∈ D.coreRegularizedImage.carrier := by
  obtain ⟨a,ha,hCore,he⟩ := (D.mem_coreRegularizedImage h00 q).mp hq
  have hd : rv M d=rv M ((D.point a).1 D.coordinate) :=
    hrv.trans (congrArg (fun p => rv M (p.1 D.coordinate)) he.symm)
  have hmem := D.core_image_saturated ha hCore d hd
  rw [D.image_carrier] at hmem
  obtain ⟨b,hb,hPoint⟩ := hmem
  have hCoreB : D.core b=true := by
    have hh := congrArg (fun p : Mixed M (n+1) (1+r) => p.2 (Fin.castAdd r (0 : Fin 1))) hPoint
    simp only [point,Fin.append_left,hCore] at hh
    exact branchTag_injective h00 hh
  apply (D.mem_coreRegularizedImage h00 _).mpr
  refine ⟨b,hb,hCoreB,?_⟩
  rw [hPoint,regularize_coordinate_replacement _ _ _ hd,he]

theorem variableReleasedImage_leading_tag_row
    (D : CentripetalData (G := G) A) (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S)
    (q : Mixed M (n+1) ((n+1)+(1+r))) (hq : q ∈ (D.variableReleasedImage U).carrier) :
    rv M (q.1 D.coordinate)=q.2 (Fin.castAdd (1+r) D.coordinate) := by
  obtain ⟨a,ha,hU,rfl⟩ := (D.mem_variableReleasedImage U q).mp hq
  simp only [regularize,Fin.append_left]
  rfl

theorem variableReleasedImage_replace_row
    (D : CentripetalData (G := G) A) (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S)
    (ρ : (Fin r → RVInfinity M) → Gamma M) (H : VariableApertureReleaseData D U ρ)
    (q : Mixed M (n+1) ((n+1)+(1+r))) (hq : q ∈ (D.variableReleasedImage U).carrier)
    (d : VF M) (hrv : rv M d=rv M (q.1 D.coordinate)) :
    (Function.update q.1 D.coordinate d,q.2) ∈ (D.variableReleasedImage U).carrier := by
  obtain ⟨a,ha,hU,he⟩ := (D.mem_variableReleasedImage U q).mp hq
  obtain ⟨hu,hOld,hNew⟩ := (H.labels a ha).mp hU
  have hd : rv M d=rv M ((D.point a).1 D.coordinate) :=
    hrv.trans (congrArg (fun p => rv M (p.1 D.coordinate)) he.symm)
  obtain ⟨b,hb,hTags,hbU,hbOld,hbNew,hPoint⟩ :=
    D.variable_aperture_coordinate_replacement ρ H.stable a ha hu hOld hNew d hd
  apply (D.mem_variableReleasedImage U _).mpr
  refine ⟨b,hb,(H.labels b hb).mpr ⟨hbU,hbOld,hbNew⟩,?_⟩
  rw [hPoint,regularize_coordinate_replacement _ _ _ hd,he]

end CentripetalData

theorem synchronized_core_in_arbitrary_coordinate_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (D : CentripetalData (G := G) A)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (e : Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n)=D.coordinate)
    (F : PreparedSynchronizedFamily (G := G) (coordinateProjection D.coreRegularizedImage e)
      (fun i => coordinateProjection (E i).coreRegularizedImage e)
      (fun i => coordinateProjection_subset ((hRestr i).core_image_subset h00) e)) :
    Nonempty (PreparedSynchronizedFamily (G := G) D.coreRegularizedImage
      (fun i => (E i).coreRegularizedImage) (fun i => (hRestr i).core_image_subset h00)) := by
  apply synchronized_coordinate_bundle_of_projected_preparation h00 hc hκ hs hv
    D.coreRegularizedImage (D.coreRegularizedImage_properInvariant h00 hc hκ hs hv)
    D.coreRegularizedImage_doublyBounded _ (fun i => (hRestr i).core_image_subset h00)
    e (Fin.castAdd (1+r) D.coordinate) _ _ F
  · exact reindexed_coordinate_bundle_of_replacement _ e D.coordinate he _
      (D.coreRegularizedImage_leading_tag_row h00) (D.coreRegularizedImage_replace_row h00)
  · intro i
    have hj : e (Fin.last n)=(E i).coordinate := he.trans (hRestr i).coordinate.symm
    have h := reindexed_coordinate_bundle_of_replacement _ e (E i).coordinate hj _
      ((E i).coreRegularizedImage_leading_tag_row h00) ((E i).coreRegularizedImage_replace_row h00)
    simpa only [(hRestr i).coordinate] using h

theorem synchronized_variable_release_in_arbitrary_coordinate_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S)
    (ρ : (Fin r → RVInfinity M) → Gamma M) (H : VariableApertureReleaseData D U ρ)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (hStable : ∀ i,∀ a ∈ (P i).carrier,a.2 ∈ D.activeTags.carrier → ∀ x : VF M,
      (ρ a.2).val < vfValue (a.1 D.coordinate-x) →
        (Function.update a.1 D.coordinate x,a.2) ∈ (P i).carrier)
    (e : Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n)=D.coordinate)
    (F : PreparedSynchronizedFamily (G := G) (coordinateProjection (D.variableReleasedImage U) e)
      (fun i => coordinateProjection ((E i).variableReleasedImage U) e)
      (fun i => coordinateProjection_subset ((hRestr i).variable_released_image_subset U) e)) :
    Nonempty (PreparedSynchronizedFamily (G := G) (D.variableReleasedImage U)
      (fun i => (E i).variableReleasedImage U) (fun i => (hRestr i).variable_released_image_subset U)) := by
  apply synchronized_coordinate_bundle_of_projected_preparation h00 hc hκ hs hv
    (D.variableReleasedImage U) (D.variableReleasedImage_properInvariant h00 hc hκ hs hv U)
    (D.variableReleasedImage_doublyBounded U) _ (fun i => (hRestr i).variable_released_image_subset U)
    e (Fin.castAdd (1+r) D.coordinate) _ _ F
  · exact reindexed_coordinate_bundle_of_replacement _ e D.coordinate he _
      (D.variableReleasedImage_leading_tag_row U) (D.variableReleasedImage_replace_row U ρ H)
  · intro i
    have hj : e (Fin.last n)=(E i).coordinate := he.trans (hRestr i).coordinate.symm
    have h := reindexed_coordinate_bundle_of_replacement _ e (E i).coordinate hj _
      ((E i).variableReleasedImage_leading_tag_row U)
      ((E i).variableReleasedImage_replace_row U ρ (H.restrict (hRestr i) (hStable i)))
    simpa only [(hRestr i).coordinate] using h

end DiamondIntegral.Section6
