import «section 3».MeasuredLocalMonomialCongruence
import «section 3».MeasuredNativeRESPartitions
import «section 3».NativeTensorImagePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

theorem GammaGroundRESUnitChart.measured_local_monomial_congruence
    (X Y : GammaGroundRESUnitChart hc B r)
    (s : GammaGroundMap X.native (GammaGroundDefSet.univ hc B (rawRVUnitSpace Y.arity))) (hs : Function.Injective s)
    (hsub : s.image.carrier ⊆ Y.native.carrier)
    (G : GammaGroundGammaPiece hc B n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : IsUnit A.det)
    (c : GammaGroundMap X.native (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (δ : Fin n → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hcval : ∀ a, rvUnitTupleValues (c a).val = δ)
    (f h : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) (hh : FullGammaFunction (integrationGammaBase B) h)
    (hw : ∀ γ : Fin n → Values.Gamma (M := M), γ ∈ G.carrier → f γ = h (fun i => δ i * integerMonomialMap A γ i)) :
    gammaGroundMeasuredCoefficientCongruence
      (gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf))
      (gammaGroundMeasuredRESDirectSumClass (Y.restrict s.image hsub).measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight
          (gammaGroundGammaTranslate (gammaGroundMonomialValueImage G A) δ hδ) h hh)) := by
  let es : GammaGroundBijection X.native s.image := ⟨s.toImage,s.toImage_bijective hs⟩
  let E := Y.restrict s.image hsub
  let e := E.bijection.symm.comp (es.comp X.bijection)
  exact gammaGroundMeasuredCoefficientCongruence_local_monomial X.measured E.measured
    X.measured_weight E.measured_weight e G A hA (c.comp X.bijection.map) δ hδ
      (fun a => hcval (X.bijection.map a)) f h hf hh hw
end DiamondIntegral.Section3
