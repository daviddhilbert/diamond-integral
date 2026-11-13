import «section 3».TensorTupleCoefficientCongruence
import «section 3».GammaGroundIntegralMonomialImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

theorem gammaGroundRESDirectSumClass_bijection (X Y : GammaGroundRESObject hc B r)
    (e : GammaGroundBijection X.obj.domain Y.obj.domain) :
    gammaGroundRESDirectSumClass X = gammaGroundRESDirectSumClass Y := by
  let E : X ≅ Y := (gammaGroundResProperty (hc := hc) (ground := B) (k := r)).isoMk
    (asIso (show X.obj ⟶ Y.obj from e))
  exact congrArg (DirectSum.of (GammaGroundRESKPlus hc B) r) (gammaGroundRESClass_iso E)

/-- The local unimodular product comparison follows from the elementary
coordinate pairs, the actual Gamma isomorphism and the RES bijection.
This is an equality in the generated positive congruence. -/
theorem gammaGroundUnmeasuredCoefficientCongruence_local_monomial
    (X Y : GammaGroundRESObject hc B r) (e : GammaGroundBijection X.obj.domain Y.obj.domain)
    (G : GammaGroundGammaPiece hc B n) (C : Matrix (Fin n) (Fin n) ℤ) (hC : IsUnit C.det)
    (c : GammaGroundMap X.obj.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hcval : ∀ a : X.obj.domain, rvUnitTupleValues (c a).val = δ) :
    gammaGroundUnmeasuredCoefficientCongruence
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G))
      (gammaGroundRESDirectSumClass Y ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single
          (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G C) δ hδ))) := by
  rw [← gammaGroundRESDirectSumClass_bijection X Y e,
    gammaGroundGammaSemiringClass_monomial_image G C hC]
  exact gammaGroundUnmeasuredCoefficientCongruence_tuple_translation X (gammaGroundMonomialValueImage G C)
    δ hδ ⟨c,hcval⟩
end DiamondIntegral.Section3
