import «section 6».MeasuredCoreDimensionInduction
import «section 6».VariableApertureGammaForms

/-! Lower-dimensional measured induction prepares an actual variable
old-aperture annulus in every active coordinate. Its complete Gamma
form, descended open levels, protected sets and full-disc geometry are
constructed rather than supplied as additional induction hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_variable_release_of_dimension_induction
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hIH : MeasuredFormCompatiblePreparationInDimension (G := G) S n k)
    {A : DefSet (rawMixedSpace (M := M) (n+2) r) S}
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (U : DefSet (rawRVSpace (M := M) ((n+2)+(1+r))) S)
    (ρ : (Fin r → RVInfinity M) → Gamma M) (H : VariableApertureReleaseData D U ρ)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hRestr : ∀ i,ApertureRestrictionData D (E i))
    (hStable : ∀ i,∀ a ∈ (P i).carrier,a.2 ∈ D.activeTags.carrier → ∀ x : VF M,
      (ρ a.2).val < vfValue (a.1 D.coordinate-x) → (Function.update a.1 D.coordinate x,a.2) ∈ (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (hSafe : D.VariableCoreFormConstant ρ ω)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) (D.variableReleasedImage U)
        (fun i => (E i).variableReleasedImage U) (fun i => (hRestr i).variable_released_image_subset U)
        (D.variableReleasedGammaForm U h00 ω),
      FormCompatibleSynchronizedChain (G := G) (Fin k) (D.variableReleasedImage U) T.target T.map
        (fun i => (E i).variableReleasedImage U) (D.variableReleasedGammaForm U h00 ω) := by
  let e := Equiv.swap (Fin.last (n+1)) D.coordinate
  have he : e (Fin.last (n+1))=D.coordinate := Equiv.swap_apply_left _ _
  have hRelease := D.variableReleasedImage_properInvariant h00 hc hκ hs hv U
  have hGeometry := D.variableReleasedGammaForm_levels_geometry U h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  have hReleaseLevels := fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen
  obtain ⟨η,hη,hηLevels⟩ := (D.variableReleasedGammaForm_coordinate_constant U h00 ρ H ω hSafe).exists_coordinate_descent
    h00 hc linear hκ hs hv hsmall hΓ hRelease e he hReleaseLevels
  have hRP : IsRVPullback (D.variableReleasedImage U).carrier :=
    focusActive_rvPullback _ U (D.regularized_image_rvPullback h00 hARV)
  obtain ⟨F,hF⟩ := hIH _ (coordinateProjection (D.variableReleasedImage U) e)
    (coordinateProjection_properInvariant _ e hRelease)
    (coordinateProjection_doublyBounded _ e (D.variableReleasedImage_doublyBounded U))
    (vfDropLast_image_rvPullback (reindexedVFSet_rvPullback _ e hRP))
    (fun i => coordinateProjection ((E i).variableReleasedImage U) e)
    (fun i => coordinateProjection_subset ((hRestr i).variable_released_image_subset U) e)
    (fun i => coordinateProjection_properInvariant _ e
      ((E i).variableReleasedImage_properInvariant h00 hc hκ hs hv U)) η hηLevels
  apply measured_form_compatible_coordinate_bundle_of_projected_preparation h00 hc hκ hs hv
    (D.variableReleasedImage U) hRelease (D.variableReleasedImage_doublyBounded U)
    _ (fun i => (hRestr i).variable_released_image_subset U) e (Fin.castAdd (1+r) D.coordinate)
    _ _ (D.variableReleasedGammaForm U h00 ω) η hη F hF
  · exact reindexed_coordinate_bundle_of_replacement _ e D.coordinate he _
      (D.variableReleasedImage_leading_tag U) (D.variableReleasedImage_replace U ρ H)
  · intro i
    have hj : e (Fin.last (n+1))=(E i).coordinate := he.trans (hRestr i).coordinate.symm
    have h := reindexed_coordinate_bundle_of_replacement _ e (E i).coordinate hj _
      ((E i).variableReleasedImage_leading_tag U)
      ((E i).variableReleasedImage_replace U ρ (H.restrict (hRestr i) (hStable i)))
    simpa only [(hRestr i).coordinate] using h

end DiamondIntegral.Section6
