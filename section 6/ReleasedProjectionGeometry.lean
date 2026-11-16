import «section 6».ReleasedCoordinateBundles

/-! Proper invariance, double bounds and taggedness of the actual
released image and its lower-dimensional projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem releasedRegularizedImage_subset (D E : CentripetalData (G := G) A) :
    (D.releasedRegularizedImage E).carrier ⊆ (regularizeMap E.map.image).image.carrier := by
  intro q hq
  obtain ⟨a,ha,hOld,hNew,he⟩ := (D.mem_releasedRegularizedImage E q).mp hq
  exact ⟨E.bijection ⟨a,ha⟩,he⟩

theorem releasedRegularizedImage_doublyBounded (D E : CentripetalData (G := G) A) :
    VFDoublyBounded (D.releasedRegularizedImage E).carrier := by
  obtain ⟨γ,hγ⟩ := regularized_vfDoublyBounded E.image_vfDoublyBounded
  exact ⟨γ,fun q hq => hγ q (D.releasedRegularizedImage_subset E hq)⟩

theorem releasedRegularizedImage_tagged (D E : CentripetalData (G := G) A) :
    ∀ p ∈ (D.releasedRegularizedImage E).carrier, ∀ q ∈ (D.releasedRegularizedImage E).carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  have ht : ∀ p ∈ (regularizeMap E.map.image).image.carrier,
      ∀ q ∈ (regularizeMap E.map.image).image.carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
    rw [regularization_carrier]
    exact regularized_tagged _
  exact fun p hp q hq => ht p (D.releasedRegularizedImage_subset E hp)
    q (D.releasedRegularizedImage_subset E hq)

theorem releasedRegularizedImage_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D E : CentripetalData (G := G) A) : ProperInvariant S (D.releasedRegularizedImage E).carrier := by
  have hf : SpecialCovariantChain (G := G) A (regularizeMap E.map.image).image
      ((regularization E.map.image).comp E.bijection) :=
    .comp (.centripetal A E) (.regularize E.map.image
      (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded)
  have h := (hf.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ).restrict
    h00 hc linear hκ hs hv hsmall hΓ (D.releasedDomain E) (D.releasedDomain_subset E)
    (D.releasedDomain_properInvariant h00 hc hκ hs hv E)
  exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective

variable {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def releasedProjection (D E : CentripetalData (G := G) B) :=
  (vfDropLast (D.releasedRegularizedImage E)).image

theorem releasedProjection_doublyBounded (D E : CentripetalData (G := G) B) :
    VFDoublyBounded (D.releasedProjection E).carrier :=
  vfDropLast_image_doublyBounded (D.releasedRegularizedImage_doublyBounded E)

theorem releasedProjection_tagged (D E : CentripetalData (G := G) B) :
    ∀ p ∈ (D.releasedProjection E).carrier, ∀ q ∈ (D.releasedProjection E).carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 :=
  vfDropLast_image_tagged (D.releasedRegularizedImage_tagged E)

theorem releasedProjection_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D E : CentripetalData (G := G) B) : ProperInvariant S (D.releasedProjection E).carrier :=
  vfDropLast_image_properInvariant
    (D.releasedRegularizedImage_properInvariant h00 hc linear hκ hs hv hsmall hΓ E)

end DiamondIntegral.Section6.CentripetalData
