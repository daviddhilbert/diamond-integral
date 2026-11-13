import «section 3».GammaGroundGammaRVMonicity
import «section 3».GammaGroundFiniteGammaSquare
import «section 3».GammaGroundFiniteGammaPositiveComparison
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Upper horizontal injectivity holds before group completion and in
each original object degree. -/
theorem gammaGroundFiniteGammaToRESKPlus_injective [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin n → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b)) :
    Function.Injective (gammaGroundFiniteGammaToRESKPlus (hc := hc) (ground := B) (k := n)) := by
  intro a b hab
  apply gammaGroundFiniteGammaToGammaKPlus_injective
  apply gammaGroundGammaToRVKPlus_injective hκ hs h00 hsmall hγsmall RY
  have h := congrArg gammaGroundRESToRVKPlus hab
  have ha := DFunLike.congr_fun (gammaGroundFiniteGamma_positive_square (hc := hc) (ground := B)) a
  have hb := DFunLike.congr_fun (gammaGroundFiniteGamma_positive_square (hc := hc) (ground := B)) b
  exact ha.symm.trans (h.trans hb)

end DiamondIntegral.Section3
