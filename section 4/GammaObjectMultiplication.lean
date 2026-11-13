import «section 4».GammaProfileProducts

/-! The actual homogeneous object assignment preserves products and the
degree-zero unit, with the proved original-base coefficient restriction. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaObjectMultiplication
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaProfileProducts
open GammaObjectPolynomial GammaFunctionPolynomial GammaSumMap GammaDefinableConvolution EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem profileCoefficient_product (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (μ : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hσ : MapDefinable B σ) :
    profileCoefficient h00 hκ hs B hr hγ k (productSet I J) (productSet_definable B I hI J hJ)
      (sumMap μ σ) (sumMap_definable B μ σ hμ hσ) =
    profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ * profileCoefficient h00 hκ hs B hr hγ k J hJ σ hσ := by
  apply Subtype.ext
  exact profile_product h00 linear hκ hs B hr hγ hΓ k n m I hI J hJ μ hμ σ hσ

theorem objectPolynomial_product (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (μ : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hσ : MapDefinable B σ) :
    objectPolynomial h00 hκ hs B hr hγ k (n + m) (productSet I J) (productSet_definable B I hI J hJ)
      (sumMap μ σ) (sumMap_definable B μ σ hμ hσ) =
    objectPolynomial h00 hκ hs B hr hγ k m I hI μ hμ * objectPolynomial h00 hκ hs B hr hγ k n J hJ σ hσ := by
  apply Subtype.ext
  change Polynomial.monomial (n + m)
      (profileCoefficient h00 hκ hs B hr hγ k (productSet I J) (productSet_definable B I hI J hJ)
        (sumMap μ σ) (sumMap_definable B μ σ hμ hσ)) =
    Polynomial.monomial m (profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ) *
      Polynomial.monomial n (profileCoefficient h00 hκ hs B hr hγ k J hJ σ hσ)
  rw [Polynomial.monomial_mul_monomial, Nat.add_comm m n,
    profileCoefficient_product h00 linear hκ hs B hr hγ hΓ k n m I hI J hJ μ hμ σ hσ]

theorem objectPolynomial_one (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) :
    objectPolynomial h00 hκ hs B hr hγ k 0 Set.univ (GammaIntegerFamilies.univ_definable_base B 0)
      (fun _ => 1) (constant_definable B 1 (GammaGroupNames.one_definable_base B)) = 1 := by
  have hc : profileCoefficient h00 hκ hs B hr hγ k Set.univ (GammaIntegerFamilies.univ_definable_base B 0)
      (fun _ => 1) (constant_definable B 1 (GammaGroupNames.one_definable_base B)) = 1 := by
    apply Subtype.ext
    change (profile h00 hκ hs B hr hγ k Set.univ (GammaIntegerFamilies.univ_definable_base B 0)
      (fun _ => 1) (constant_definable B 1 (GammaGroupNames.one_definable_base B))).val = 1
    rw [GammaZeroDegreeProfile.profile_zero_degree]
    simp [toPaperGamma_one, point_zero]
  apply Subtype.ext
  change Polynomial.monomial 0 _ = 1
  rw [hc, Polynomial.monomial_zero_one]

end DiamondIntegral.Section4.GammaObjectMultiplication
