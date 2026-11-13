import «section 3».GammaGroundRVGenericInverse
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- An actual bijection of full RV preimages induces an interpreted
Gamma bijection over exactly the original ground. Existence of a full
RV lift of this generic bijection is not asserted here. -/
theorem gammaGroundRVBijection_generic_bijection {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
    (f : GammaGroundBijection (gammaGroundRVUnitGammaPreimage G) (gammaGroundRVUnitGammaPreimage J)) :
    ∃ h : GammaGroundBijection G J,
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        (((gammaGroundFullPreimageValueMap J).comp f.map).equalizer
          (h.map.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier := by
  obtain ⟨h,hh⟩ := gammaGroundRVMap_generic_contraction hκ hs h00 hsmall hγsmall G J f.map
  obtain ⟨k,hk⟩ := gammaGroundRVMap_generic_contraction hκ hs h00 hsmall hγsmall J G f.symm.map
  have hleft : ∀ γ : G, k (h γ) = γ :=
    gammaGroundRVGeneric_inverse_at hκ hs h00 hsmall G J f h k hh hk
  have hright : ∀ γ : J, h (k γ) = γ := by
    intro γ
    have hff : f.symm.symm = f := by
      apply GammaGroundBijection.ext
      apply GammaGroundMap.ext
      intro a
      apply f.symm.bijective.1
      exact (f.symm.map.apply_inverse f.symm.bijective a).trans
        (f.map.inverse_apply f.bijective a).symm
    have hhh : (gammaGroundRVGenericValueImage hs h00 B hsmall
        (((gammaGroundFullPreimageValueMap J).comp f.symm.symm.map).equalizer
          (h.comp (gammaGroundFullPreimageValueMap G)))).carrier = G.carrier := by
      rw [hff]
      exact hh
    exact gammaGroundRVGeneric_inverse_at hκ hs h00 hsmall J G f.symm k h hk hhh γ
  exact ⟨⟨h,⟨Function.LeftInverse.injective hleft,Function.RightInverse.surjective hright⟩⟩,hh⟩

end DiamondIntegral.Section3
