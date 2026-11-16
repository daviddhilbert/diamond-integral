import «section 6».ReleasedGammaLevelGeometry

/-! The actual retained core has an original-base transported Gamma
form, which descends through its coordinate projection whenever the
old aperture lies inside a common form-constancy radius. The descended
form has open levels and exact values, as needed for measured induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def coreGammaForm (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map D.coreRegularizedImage (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))).comp
    (Map.inclusion D.coreRegularizedImage_subset)

theorem coreGammaForm_projection_constant
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u)) :
    ∀ q ∈ D.coreRegularizedImage.carrier,∀ q' ∈ D.coreRegularizedImage.carrier,
      Fin.init q.1=Fin.init q'.1 → q.2=q'.2 →
      gammaFormExtension (D.coreGammaForm h00 ω) q=gammaFormExtension (D.coreGammaForm h00 ω) q' := by
  intro q hq q' hq' hInit hTags
  let x : (regularizeMap D.map.image).image := ⟨q,D.coreRegularizedImage_subset hq⟩
  let y : (regularizeMap D.map.image).image := ⟨q',D.coreRegularizedImage_subset hq'⟩
  have h := D.coordinate_step_inverse_form_constant_on_core h00 hj δ hCut ω hConst x y hInit hTags hq.2
  rw [gammaFormExtension_at _ x,gammaFormExtension_at _ y] at h
  rw [gammaFormExtension_at _ ⟨q,hq⟩,gammaFormExtension_at _ ⟨q',hq'⟩]
  exact h

theorem coreGammaForm_levels_geometry
    (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∀ γ,ProperInvariantGeometry {q | q ∈ D.coreRegularizedImage.carrier ∧
      gammaFormExtension (D.coreGammaForm h00 ω) q=γ} := by
  have hStep : SpecialCovariantChain (G := G) A (regularizeMap D.map.image).image
      (centripetalStepMap D) :=
    .comp (.centripetal A D) (.regularize D.map.image
      (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded)
  have hGeometry := hStep.gamma_levels_proper_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  intro γ
  exact gammaFormRestriction_level_geometry D.coreRegularizedImage_subset
    (D.coreRegularizedImage_properInvariant h00 hc hκ hs hv).geometry
    (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))) γ (hGeometry γ)

theorem exists_core_gamma_descent_with_open_levels
    (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hj : D.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∃ η : Map D.coreProjection (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ q : D.coreRegularizedImage,η ((vfDropLast D.coreRegularizedImage).toImage q)=D.coreGammaForm h00 ω q) ∧
      ∀ u γ,IsOpen {b : Fin n → VF M | (b,u) ∈ D.coreProjection.carrier ∧ gammaFormExtension η (b,u)=γ} := by
  let h := D.coreGammaForm_projection_constant h00 hj δ hCut ω hConst
  let η := coordinateGammaDescent (D.coreGammaForm h00 ω) h
  have hη := coordinateGammaDescent_at (D.coreGammaForm h00 ω) h
  have hGeometry := D.coreGammaForm_levels_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  exact ⟨η,hη,descended_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ
    (D.coreRegularizedImage_properInvariant h00 hc hκ hs hv)
    (D.coreGammaForm h00 ω) (fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen) η hη⟩

end DiamondIntegral.Section6.CentripetalData
