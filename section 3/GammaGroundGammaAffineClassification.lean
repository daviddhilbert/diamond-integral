import «section 3».GammaGroundGammaHomGenericLift
import «section 3».GammaGroundPiecewiseGLZLift
import «section 3».GammaGroundUnitFamilyOriginalWeights
import «section 3».GammaGroundCoefficientMonicityContext
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {A D : GammaGroundGammaObject hc B n}

/-- The given Gamma morphism is piecewise GL(Z) over its complete
original mixed ground. This local proof uses the approved diagonal
classification and no [19] or HK premise. -/
theorem gammaGroundGammaHom_piecewiseGLZ [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (g : GammaGroundGammaHom A D) : GammaGroundPiecewiseGLZ g.bijection := by
  obtain ⟨L,hh⟩ := g.exists_generic_unit_family_lift hκ hs h00 hsmall
  apply gammaGroundPiecewiseGLZ_of_pointwise hκ.le hs hsmall hγsmall g.bijection
  intro γ
  obtain ⟨C,c,hC,_,hcoeff,hcdef⟩ := gammaGroundUnitFamily_generic_original_coefficients
    hκ hs h00 hsmall RY A D L.toFamilyMap L.equiv.injective g.bijection.toFamilyMap hh γ
  exact ⟨⟨C,hC,c,hcdef⟩,hcoeff⟩

/-- Full-preimage Gamma morphisms are exactly the definably piecewise
unimodular transformations with actual old-ground RV translations. -/
theorem gammaGroundGammaHom_iff_piecewiseGLZ [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (H : GammaGroundFamilyBijection A D) :
    (∃ g : GammaGroundGammaHom A D, g.bijection = H) ↔ GammaGroundPiecewiseGLZ H := by
  constructor
  · rintro ⟨g,rfl⟩
    exact gammaGroundGammaHom_piecewiseGLZ hκ hs h00 hsmall hγsmall RY g
  · exact gammaGroundGammaHom_of_piecewiseGLZ hκ.le hs hsmall hγsmall H

/-- The full-ground classification specializes to the manuscript context
without any stronger real-base generation or representative choice. -/
theorem gammaGroundContext_GammaHom_iff_piecewiseGLZ
    (C : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (RY : GammaGroundCoefficientClassification C) {n : ℕ}
    {A D : GammaGroundGammaObject hc C.base n} (H : GammaGroundFamilyBijection A D) :
    (∃ g : GammaGroundGammaHom A D, g.bijection = H) ↔ GammaGroundPiecewiseGLZ H := by
  letI : CharZero (ModelResidue M) := rvResidueField_charZero C.model00
  exact gammaGroundGammaHom_iff_piecewiseGLZ C.uncountable C.saturated C.model00 C.small_real C.small_gamma (RY n) H

end DiamondIntegral.Section3
