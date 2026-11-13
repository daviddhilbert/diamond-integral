import «section 3».PositiveTensorDescent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {R : Type} [CommSemiring R]

/-- Numerical Gamma evaluations may be invariant under all original-
ground definable translations, including those without an RV lift. -/
def GammaGroundGammaEvaluationTranslationInvariant
    (g : GammaGroundGammaPositiveSemiring hc B →+* R) : Prop :=
  ∀ (n : ℕ) (G H : GammaGroundGammaPiece hc B n) (δ : Fin n → Values.Gamma (M := M)),
    (∀ i, GammaParameters.GammaDefinableClosureAtBase B (δ i)) →
    (∀ γ : Fin n → Values.Gamma (M := M), γ ∈ G.carrier ↔ (fun i => δ i * γ i) ∈ H.carrier) →
    g (gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G)) =
      g (gammaGroundGammaSemiringClass (GammaGroundGammaObject.single H))

theorem gammaGroundBalancedEvaluation_respects_coefficient_pairs
    (q : GammaGroundRESDirectSum hc B →+* R) (g : GammaGroundGammaPositiveSemiring hc B →+* R)
    (hcomm : q.comp gammaGroundFiniteGammaToRESSemiring = g.comp gammaGroundFiniteGammaToGammaSemiring)
    (htrans : GammaGroundGammaEvaluationTranslationInvariant g)
    {a b : GammaGroundUnmeasuredPositiveTensor hc B} (hab : gammaGroundUnmeasuredCoefficientPair a b) :
    balancedSquareMap q g hcomm a = balancedSquareMap q g hcomm b := by
  obtain ⟨r,n,i,X,G,H,δ,_,hδ,_,hshift,rfl,rfl⟩ := hab
  rw [balancedSquareMap_tmul,balancedSquareMap_tmul,htrans n G H δ hδ hshift]

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

/-- A balanced translation-invariant evaluation descends already from
the positive tensor semiring. The target may itself be a ring, but no
groupification of the source is used to define this map. -/
def gammaGroundBalancedEvaluationOnRV
    (q : GammaGroundRESDirectSum hc B →+* R) (g : GammaGroundGammaPositiveSemiring hc B →+* R)
    (hcomm : q.comp gammaGroundFiniteGammaToRESSemiring = g.comp gammaGroundFiniteGammaToGammaSemiring)
    (htrans : GammaGroundGammaEvaluationTranslationInvariant g) :
    GammaGroundRVPositiveSemiring hc B →+* R :=
  gammaGroundUnmeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ (balancedSquareMap q g hcomm)
    (fun _ _ hab => gammaGroundBalancedEvaluation_respects_coefficient_pairs q g hcomm htrans hab)

@[simp] theorem gammaGroundBalancedEvaluationOnRV_tensor
    (q : GammaGroundRESDirectSum hc B →+* R) (g : GammaGroundGammaPositiveSemiring hc B →+* R)
    (hcomm : q.comp gammaGroundFiniteGammaToRESSemiring = g.comp gammaGroundFiniteGammaToGammaSemiring)
    (htrans : GammaGroundGammaEvaluationTranslationInvariant g)
    (a : GammaGroundRESDirectSum hc B) (b : GammaGroundGammaPositiveSemiring hc B) :
    gammaGroundBalancedEvaluationOnRV hκ hs h00 hsmall hγsmall hΓ q g hcomm htrans
      (gammaGroundUnmeasuredTensorMap (a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] b)) = q a * g b :=
  gammaGroundUnmeasuredTensorDescend_image hκ hs h00 hsmall hγsmall hΓ _ _ _

/-- On actual product lifts the descended evaluation has exactly the
original RES/Gamma product formula. -/
theorem gammaGroundBalancedEvaluationOnRV_objects
    (q : GammaGroundRESDirectSum hc B →+* R) (g : GammaGroundGammaPositiveSemiring hc B →+* R)
    (hcomm : q.comp gammaGroundFiniteGammaToRESSemiring = g.comp gammaGroundFiniteGammaToGammaSemiring)
    (htrans : GammaGroundGammaEvaluationTranslationInvariant g) {r n : ℕ}
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaObject hc B n) :
    gammaGroundBalancedEvaluationOnRV hκ hs h00 hsmall hγsmall hΓ q g hcomm htrans
      (gammaGroundRVSemiringClass (X.obj.product G.rvLift)) =
      q (gammaGroundRESDirectSumClass X) * g (gammaGroundGammaSemiringClass G) := by
  rw [← gammaGroundUnmeasuredTensorMap_objects]
  exact gammaGroundBalancedEvaluationOnRV_tensor hκ hs h00 hsmall hγsmall hΓ q g hcomm htrans _ _

/-- Restriction to RES is the prescribed original coefficient map;
no additional target quotient is imposed by tensor-kernel descent. -/
theorem gammaGroundBalancedEvaluationOnRV_on_RES
    (q : GammaGroundRESDirectSum hc B →+* R) (g : GammaGroundGammaPositiveSemiring hc B →+* R)
    (hcomm : q.comp gammaGroundFiniteGammaToRESSemiring = g.comp gammaGroundFiniteGammaToGammaSemiring)
    (htrans : GammaGroundGammaEvaluationTranslationInvariant g) :
    (gammaGroundBalancedEvaluationOnRV hκ hs h00 hsmall hγsmall hΓ q g hcomm htrans).comp
      gammaGroundRESToRVSemiring = q := by
  apply RingHom.ext
  intro a
  have h := gammaGroundBalancedEvaluationOnRV_tensor hκ hs h00 hsmall hγsmall hΓ q g hcomm htrans a 1
  simpa only [gammaGroundUnmeasuredTensorMap_tmul,map_one,mul_one,RingHom.comp_apply] using h

theorem gammaGroundBalancedEvaluationOnRV_unique
    (q : GammaGroundRESDirectSum hc B →+* R) (g : GammaGroundGammaPositiveSemiring hc B →+* R)
    (hcomm : q.comp gammaGroundFiniteGammaToRESSemiring = g.comp gammaGroundFiniteGammaToGammaSemiring)
    (htrans : GammaGroundGammaEvaluationTranslationInvariant g)
    (F : GammaGroundRVPositiveSemiring hc B →+* R)
    (hF : ∀ a b, F (gammaGroundUnmeasuredTensorMap
      (a ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B] b)) = q a * g b) :
    F = gammaGroundBalancedEvaluationOnRV hκ hs h00 hsmall hγsmall hΓ q g hcomm htrans := by
  apply gammaGroundUnmeasuredTensorDescend_unique hκ hs h00 hsmall hγsmall hΓ
    (balancedSquareMap q g hcomm) _ F
  exact balancedSquareMap_unique q g hcomm (F.comp gammaGroundUnmeasuredTensorMap) hF
end DiamondIntegral.Section3
