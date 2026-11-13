import «section 3».GammaGroundUnitFamilyGenericInverse
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

/-- Bijections of full tagged RV families induce interpreted Gamma
family bijections over the same ground, including the finite tags. -/
theorem gammaGroundUnitFamily_generic_bijection {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundFamilyBijection A.unitFamily D.unitFamily) :
    ∃ H : GammaGroundFamilyBijection A D, ∀ i,
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        ((D.unitValueFamilyMap.comp F.toFamilyMap).equalizerPiece
          (H.toFamilyMap.comp A.unitValueFamilyMap) i)).carrier = (A.piece i).carrier := by
  obtain ⟨H,hh⟩ := gammaGroundUnitFamily_generic_contraction hκ hs h00 hsmall hγsmall A D F.toFamilyMap
  obtain ⟨K,hk⟩ := gammaGroundUnitFamily_generic_contraction hκ hs h00 hsmall hγsmall D A F.symm.toFamilyMap
  have hleft : Function.LeftInverse K.toFun H.toFun :=
    gammaGroundUnitFamily_generic_inverse_at hκ hs h00 hsmall A D F H K hh hk
  have hright : Function.RightInverse K.toFun H.toFun := by
    intro γ
    have hFF : F.symm.symm = F := by
      apply GammaGroundFamilyBijection.ext
      exact Equiv.symm_symm F.equiv
    have hhh : ∀ i, (gammaGroundRVGenericValueImage hs h00 B hsmall
        ((D.unitValueFamilyMap.comp F.symm.symm.toFamilyMap).equalizerPiece
          (H.comp A.unitValueFamilyMap) i)).carrier = (A.piece i).carrier := by
      rw [hFF]
      exact hh
    exact gammaGroundUnitFamily_generic_inverse_at hκ hs h00 hsmall D A F.symm K H hk hhh γ
  let E : A.Carrier ≃ D.Carrier := Equiv.ofBijective H.toFun ⟨hleft.injective,hright.surjective⟩
  exact ⟨⟨E,H.definable⟩,hh⟩

end DiamondIntegral.Section3
