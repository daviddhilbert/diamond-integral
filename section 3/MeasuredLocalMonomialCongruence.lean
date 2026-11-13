import «section 3».MeasuredGammaWeightTranslations
import «section 3».MeasuredGammaMonomialWeights
import «section 3».MeasuredDegreeZeroWeightScalars
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

theorem gammaGroundMeasuredRESDirectSumClass_weight_bijection (X Y : GammaGroundMeasuredRESObject hc B r)
    (e : GammaGroundBijection X.obj.underlying.domain Y.obj.underlying.domain)
    (hw : ∀ a, X.obj.combinedWeight a = Y.obj.combinedWeight (e.map a)) :
    gammaGroundMeasuredRESDirectSumClass X = gammaGroundMeasuredRESDirectSumClass Y := by
  let f : GammaGroundMeasuredRVHom X.obj Y.obj := ⟨e,hw⟩
  let E : X ≅ Y := gammaGroundMeasuredResProperty.isoMk (asIso (show X.obj ⟶ Y.obj from f))
  exact congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) r) (gammaGroundMeasuredRESClass_iso E)

/-- On normalized RES factors, every compatible weighted unimodular
local product comparison follows from the explicit positive coordinate
relations and genuine measured Gamma and RES isomorphisms. -/
theorem gammaGroundMeasuredCoefficientCongruence_local_monomial
    (X Y : GammaGroundMeasuredRESObject hc B r)
    (hX : ∀ a, X.obj.combinedWeight a = 1) (hY : ∀ a, Y.obj.combinedWeight a = 1)
    (e : GammaGroundBijection X.obj.underlying.domain Y.obj.underlying.domain)
    (G : GammaGroundGammaPiece hc B n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det)
    (c : GammaGroundMap X.obj.underlying.domain (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ j, GammaDefinableClosureAtBase B (δ j))
    (hcval : ∀ a, rvUnitTupleValues (c a).val = δ)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) (hh : FullGammaFunction (integrationGammaBase B) h)
    (hw : ∀ γ : Fin n → Values.Gamma (M := M), γ ∈ G.carrier → f γ = h (fun j => δ j * integerMonomialMap A γ j)) :
    gammaGroundMeasuredCoefficientCongruence
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf))
      (gammaGroundMeasuredRESDirectSumClass Y ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight
          (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G A) δ hδ) h hh)) := by
  let g := fun η : Fin n → Values.Gamma (M := M) => h (fun j => δ j * η j)
  have hg : FullGammaFunction (integrationGammaBase B) g :=
    hh.comp (fun j η => δ j * η j) (fun j =>
      (FullGammaFunction.constant (δ j) (integrationGammaDefinable (hδ j))).mul (FullGammaFunction.proj _ j))
  have hres := gammaGroundMeasuredRESDirectSumClass_weight_bijection X Y e
    (fun a => (hX a).trans (hY (e.map a)).symm)
  have hmono := gammaGroundMeasuredGammaSemiringClass_monomial_weight G A hA f g hf hg hw
  have htarget : gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaTranslatedPiece
      (gammaGroundMonomialValueImage G A) g hg δ hδ) =
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight
        (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G A) δ hδ) h hh) := by
    apply gammaGroundMeasuredGammaSingleWeight_class_eqOn
    intro η _
    change (Fin n → Values.Gamma (M := M)) at η
    change h (fun j => δ j * ((δ j)⁻¹ * η j)) = h η
    exact congrArg h (funext (fun j => mul_inv_cancel_left _ _))
  rw [← hres,hmono,← htarget]
  exact gammaGroundMeasuredCoefficientCongruence_tuple_translation X (gammaGroundMonomialValueImage G A)
    g hg δ hδ ⟨c,hcval⟩
end DiamondIntegral.Section3
