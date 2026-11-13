import «section 3».GammaGroundGivenContractionGeneric
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- A given Gamma morphism has an actual full unit-family lift with the
same pointwise contraction, by exact transport of its defining witness. -/
theorem GammaGroundGammaHom.exists_unit_family_lift {A D : GammaGroundGammaObject hc B n}
    (g : GammaGroundGammaHom A D) :
    ∃ L : GammaGroundFamilyBijection A.unitFamily D.unitFamily,
      ∀ u, D.unitValueFamilyMap.toFun (L.equiv u) = g.bijection.equiv (A.unitValueFamilyMap.toFun u) := by
  obtain ⟨F,hF⟩ := g.contraction
  let L := D.unitCodeBijection.symm.comp (F.comp A.unitCodeBijection)
  refine ⟨L,fun u => ?_⟩
  exact (D.unitCode_inverse_decode (F.equiv (A.unitCodeBijection.equiv u))).symm.trans
    ((hF (A.unitCodeBijection.equiv u)).trans (congrArg g.bijection.equiv (A.unitCode_decode u)))

/-- The original Gamma morphism, not merely an unspecified generic
bijection, is the generic contraction of that actual full RV lift. -/
theorem GammaGroundGammaHom.exists_generic_unit_family_lift {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) {A D : GammaGroundGammaObject hc B n}
    (g : GammaGroundGammaHom A D) :
    ∃ L : GammaGroundFamilyBijection A.unitFamily D.unitFamily, ∀ i,
      (gammaGroundRVGenericValueImage hs h00 B hsmall
        ((D.unitValueFamilyMap.comp L.toFamilyMap).equalizerPiece
          (g.bijection.toFamilyMap.comp A.unitValueFamilyMap) i)).carrier = (A.piece i).carrier := by
  obtain ⟨L,hL⟩ := g.exists_unit_family_lift
  exact ⟨L,gammaGroundUnitFamily_contraction_is_generic hκ hs h00 hsmall A D g.bijection L hL⟩

end DiamondIntegral.Section3
