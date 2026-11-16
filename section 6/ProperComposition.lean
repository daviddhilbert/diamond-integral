import «section 6».GraphComposition

/-! Lemma 6.9. Fix an intermediate tag locally in both directions, then
apply the actual proper covariance criterion to the composite. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m k r s t : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {C : DefSet (rawMixedSpace (M := M) k t) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_6_9
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} {g : Map B C}
    (hf : ProperCovariantHomeomorphism f) (hg : ProperCovariantHomeomorphism g) :
    ProperCovariantHomeomorphism (g.comp f) := by
  have hbi : Function.Bijective (g.comp f) := hg.bijective.comp hf.bijective
  have hcont : GraphContinuous (g.comp f) :=
    (graphContinuous_of_properCovariant hv hg.covariant hg.continuous).comp
      (graphContinuous_of_properCovariant hv hf.covariant hf.continuous)
  have hInv : GraphContinuous ((g.comp f).inverse hbi) := by
    rw [inverse_comp_eq f g hf.bijective hg.bijective]
    exact (graphContinuous_of_properCovariant hv hf.inverseCovariant hf.inverseContinuous).comp
      (graphContinuous_of_properCovariant hv hg.inverseCovariant hg.inverseContinuous)
  have hA := hf.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hC := hg.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hg.bijective.surjective
  have hran : ∀ u w, IsOpen (graphFibreRange (g.comp f) u w) := by
    intro u w
    rw [← inverse_graphFibreSource (g.comp f) hbi u w]
    exact hInv.1 w u
  have hcov := (lemma_6_7 h00 hc hκ hs hv (g.comp f) hbi.surjective hA hC hcont.2 hcont.1).2
    hbi.injective hran
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (g.comp f) hcov hbi hcont.2

end DiamondIntegral.Section6
