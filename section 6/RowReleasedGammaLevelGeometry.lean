import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredCoordinatePreparationData
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
import «section 6».RowReleasedGammaForms

/-! (Row-form version for Remark 6.20, translated from `ReleasedGammaLevelGeometry`.)
 The actual released form and its descended projection have open
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
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaFormRestriction_level_geometry_row
    {A C : DefSet (rawMixedSpace (M := M) n r) S} (hCA : C.carrier ⊆ A.carrier)
    (hC : ProperInvariantGeometry C.carrier)
    (ω : RowFormOn A qR) (γ : Set (rawRVSpace (M := M) qR).Carrier)
    (hLevel : ProperInvariantGeometry {p | p ∈ A.carrier ∧ rowFormExtension ω p=γ}) :
    ProperInvariantGeometry {p | p ∈ C.carrier ∧
      rowFormExtension (ω.comp (Map.inclusion hCA)) p=γ} := by
  have he : {p | p ∈ C.carrier ∧ rowFormExtension (ω.comp (Map.inclusion hCA)) p=γ}=
      C.carrier ∩ {p | p ∈ A.carrier ∧ rowFormExtension ω p=γ} := by
    ext p
    constructor
    · rintro ⟨hp,hγ⟩
      refine ⟨hp,hCA hp,?_⟩
      rw [rowFormExtension_at _ ⟨p,hp⟩] at hγ
      rw [rowFormExtension_at _ ⟨p,hCA hp⟩]
      exact hγ
    · rintro ⟨hp,hpA,hγ⟩
      refine ⟨hp,?_⟩
      rw [rowFormExtension_at _ ⟨p,hp⟩]
      rw [rowFormExtension_at _ ⟨p,hpA⟩] at hγ
      exact hγ
  exact he.symm ▸ hC.inter hLevel

namespace CentripetalData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem releasedGammaForm_levels_geometry_row
    (D E : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u)=γ}) :
    ∀ γ,ProperInvariantGeometry {q | q ∈ (D.releasedRegularizedImage E).carrier ∧
      rowFormExtension (D.releasedGammaFormRow E h00 ω) q=γ} := by
  have hStep : SpecialCovariantChain (G := G) A (regularizeMap E.map.image).image
      (centripetalStepMap E) :=
    .comp (.centripetal A E) (.regularize E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded)
  have hGeometry := hStep.gamma_levels_proper_geometry_row h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  intro γ
  exact gammaFormRestriction_level_geometry_row (D.releasedRegularizedImage_subset E)
    (D.releasedRegularizedImage_properInvariant h00 hc linear hκ hs hv hsmall hΓ E).geometry
    (ω.comp ((centripetalStepMap E).inverse (centripetalStepMap_bijective_row E h00))) γ (hGeometry γ)

theorem exists_released_gamma_descent_with_open_levels_row
    (D E : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : RowFormOn A qR)
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → rowFormExtension ω (a,u)=rowFormExtension ω (b,u))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u)=γ}) :
    ∃ η : RowFormOn (D.releasedProjection E) qR,
      (∀ q : D.releasedRegularizedImage E,
        η ((vfDropLast (D.releasedRegularizedImage E)).toImage q)=D.releasedGammaFormRow E h00 ω q) ∧
      ∀ u γ,IsOpen {b : Fin n → VF M | (b,u) ∈ (D.releasedProjection E).carrier ∧ rowFormExtension η (b,u)=γ} := by
  obtain ⟨η,hη⟩ := D.exists_released_gamma_descent_row E h00 hj hE δ hCut ω hConst
  have hGeometry := D.releasedGammaForm_levels_geometry_row E h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  exact ⟨η,hη,descended_gamma_levels_open_row h00 hc linear hκ hs hv hsmall hΓ
    (D.releasedRegularizedImage_properInvariant h00 hc linear hκ hs hv hsmall hΓ E)
    (D.releasedGammaFormRow E h00 ω) (fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen) η hη⟩

end CentripetalData
end DiamondIntegral.Section6
