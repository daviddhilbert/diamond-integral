import «section 3».GammaGroundUnitFamilyGenericBijection
import «section 3».GammaGroundUnitFamilyOriginalWeights
import «section 3».GammaGroundUnitFamilyFullLift
import «section 3».GammaGroundUnitFamilyCodeTransport
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Actual lift isomorphisms reflect to Gamma-category isomorphisms,
with all finite tags and the original mixed ground retained. The full
contracting lift is constructed anew from its generic contraction. -/
theorem gammaGroundGamma_reflects_RV_lift_bijection [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (A D : GammaGroundGammaObject hc B n)
    (F : GammaGroundBijection A.rvLift.domain D.rvLift.domain) : Nonempty (A ⟶ D) := by
  let U := gammaGroundUnitFamilyBijectionOfRVLift F
  obtain ⟨H,hh⟩ := gammaGroundUnitFamily_generic_bijection hκ hs h00 hsmall hγsmall A D U
  have hpoint : ∀ γ : A.Carrier, ∃ Q : OriginalGroundAffineRVFormula hc B n,
      (H.equiv γ).2.val = rvUnitTupleValues Q.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) Q.matrix γ.2.val := by
    intro γ
    obtain ⟨C,c,hC,_,hcoeff,hcdef⟩ := gammaGroundUnitFamily_generic_original_coefficients
      hκ hs h00 hsmall RY A D U.toFamilyMap U.equiv.injective H.toFamilyMap hh γ
    exact ⟨⟨C,hC,c,hcdef⟩,hcoeff⟩
  obtain ⟨L,hL⟩ := gammaGroundUnitFamily_affine_full_lift hκ.le hs hsmall hγsmall A D H hpoint
  exact ⟨gammaGroundGammaHomOfUnitFamilyLift H L hL⟩

/-- Injectivity is already proved on the actual positive homogeneous
scissor monoids; no additive inverses or cancellation are introduced. -/
theorem gammaGroundGammaToRVKPlus_injective [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b)) :
    Function.Injective (gammaGroundGammaToRVKPlus (hc := hc) (ground := B) (k := n)) := by
  intro x y hxy
  obtain ⟨A,rfl⟩ := gammaGroundGammaClass_surjective x
  obtain ⟨D,rfl⟩ := gammaGroundGammaClass_surjective y
  simp only [gammaGroundGammaToRVKPlus_class] at hxy
  obtain ⟨e⟩ := gammaGroundRVClass_eq_iff_iso.mp hxy
  obtain ⟨g⟩ := gammaGroundGamma_reflects_RV_lift_bijection hκ hs h00 hsmall hγsmall RY A D e.hom
  exact gammaGroundGammaClass_iso (asIso g)

end DiamondIntegral.Section3
