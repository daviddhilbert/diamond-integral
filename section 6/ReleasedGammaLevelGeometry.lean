import «section 6».ReleasedGammaForms

/-! The actual released form and its descended projection have open
levels, derived from the full special map and the proper branch. No
properness or definability of an individually named Gamma level is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaFormRestriction_level_geometry
    {A C : DefSet (rawMixedSpace (M := M) n r) S} (hCA : C.carrier ⊆ A.carrier)
    (hC : ProperInvariantGeometry C.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (γ : Gamma M)
    (hLevel : ProperInvariantGeometry {p | p ∈ A.carrier ∧ gammaFormExtension ω p=γ}) :
    ProperInvariantGeometry {p | p ∈ C.carrier ∧
      gammaFormExtension (ω.comp (Map.inclusion hCA)) p=γ} := by
  have he : {p | p ∈ C.carrier ∧ gammaFormExtension (ω.comp (Map.inclusion hCA)) p=γ}=
      C.carrier ∩ {p | p ∈ A.carrier ∧ gammaFormExtension ω p=γ} := by
    ext p
    constructor
    · rintro ⟨hp,hγ⟩
      refine ⟨hp,hCA hp,?_⟩
      rw [gammaFormExtension_at _ ⟨p,hp⟩] at hγ
      rw [gammaFormExtension_at _ ⟨p,hCA hp⟩]
      exact hγ
    · rintro ⟨hp,hpA,hγ⟩
      refine ⟨hp,?_⟩
      rw [gammaFormExtension_at _ ⟨p,hp⟩]
      rw [gammaFormExtension_at _ ⟨p,hpA⟩] at hγ
      exact hγ
  exact he.symm ▸ hC.inter hLevel

namespace CentripetalData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem releasedGammaForm_levels_geometry
    (D E : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∀ γ,ProperInvariantGeometry {q | q ∈ (D.releasedRegularizedImage E).carrier ∧
      gammaFormExtension (D.releasedGammaForm E h00 ω) q=γ} := by
  have hStep : SpecialCovariantChain (G := G) A (regularizeMap E.map.image).image
      (centripetalStepMap E) :=
    .comp (.centripetal A E) (.regularize E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded)
  have hGeometry := hStep.gamma_levels_proper_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  intro γ
  exact gammaFormRestriction_level_geometry (D.releasedRegularizedImage_subset E)
    (D.releasedRegularizedImage_properInvariant h00 hc linear hκ hs hv hsmall hΓ E).geometry
    (ω.comp ((centripetalStepMap E).inverse (centripetalStepMap_bijective E h00))) γ (hGeometry γ)

theorem exists_released_gamma_descent_with_open_levels
    (D E : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∃ η : Map (D.releasedProjection E) (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ q : D.releasedRegularizedImage E,
        η ((vfDropLast (D.releasedRegularizedImage E)).toImage q)=D.releasedGammaForm E h00 ω q) ∧
      ∀ u γ,IsOpen {b : Fin n → VF M | (b,u) ∈ (D.releasedProjection E).carrier ∧ gammaFormExtension η (b,u)=γ} := by
  obtain ⟨η,hη⟩ := D.exists_released_gamma_descent E h00 hj hE δ hCut ω hConst
  have hGeometry := D.releasedGammaForm_levels_geometry E h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  exact ⟨η,hη,descended_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ
    (D.releasedRegularizedImage_properInvariant h00 hc linear hκ hs hv hsmall hΓ E)
    (D.releasedGammaForm E h00 ω) (fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen) η hη⟩

end CentripetalData
end DiamondIntegral.Section6
