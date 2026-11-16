import «section 6».RelativeApertureFibres

/-! The concrete finite-aperture lifted centripetal bijection is a proper
covariant homeomorphism. This uses complete graph fibers and the checked
clopen criterion, with the original parameter base throughout. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.RelativeApertureData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem image_vfBounded (D : RelativeApertureData (G := G) A) : VFBounded D.map.image.carrier := by
  obtain ⟨γ,hγ⟩ := D.image_vfDoublyBounded
  exact ⟨γ⁻¹,fun p hp i => (hγ p hp i).1⟩

theorem image_properInvariant (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ProperInvariant S D.map.image.carrier := by
  apply (lemma_6_5 h00 hc hκ hs hv _ D.map.image.definable D.image_vfBounded D.image_rvDoublyBounded).mpr
  intro v
  rw [D.image_fibre]
  exact D.graphRange_isClopen h00 hc hκ hs hv _ _

theorem properCovariant (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) : ProperCovariant D.bijection :=
  (lemma_6_7 h00 hc hκ hs hv D.bijection (D.bijective h00).surjective
    D.sourceProper (D.image_properInvariant h00 hc hκ hs hv) (D.graph_continuous h00 hv)
    (fun u v => (D.graphSource_isClopen h00 hv u v).isOpen)).1
      (D.graphRange_isClopen h00 hc hκ hs hv)

theorem properHomeomorphism (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) : ProperCovariantHomeomorphism D.bijection :=
  properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    D.bijection (D.properCovariant h00 hc hκ hs hv) (D.bijective h00) (D.graph_continuous h00 hv)

end DiamondIntegral.Section6.RelativeApertureData
