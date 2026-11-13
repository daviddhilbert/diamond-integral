import «section 4».GammaObjectMultiplication
import «section 4».GammaProfileScissors
import «section 4».GammaProfileRestrictions

/-! The homogeneous actual object assignment respects volume-preserving
definable bijections, scissors, empty domains and weight restriction. These
are proved relations for later Grothendieck presentation descent. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaObjectRelations
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaObjectPolynomial GammaObjectMultiplication
open GammaMeasuredProfileInvariance GammaProfileScissors GammaProfileRestrictions GammaBijectiveRelations
open GammaDefinableConvolution

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem objectPolynomial_volume_bijOn (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (μ σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : MapDefinable B μ) (hσ : MapDefinable B σ)
    (φ : (Fin n → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hφ : GammaDefinable B (graphOn I φ)) (hbij : Set.BijOn φ I J)
    (hvol : ∀ u ∈ I, μ u = σ (φ u) * (∏ i, φ u i) / (∏ i, u i)) :
    objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ = objectPolynomial h00 hκ hs B hr hγ k n J hJ σ hσ := by
  have he : profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ =
      profileCoefficient h00 hκ hs B hr hγ k J hJ σ hσ := by
    apply Subtype.ext
    exact congrArg Subtype.val (profile_volume_bijOn h00 linear hκ hs B hr hγ hΓ k n n
      I hI J hJ μ hμ σ hσ φ hφ hbij hvol)
  apply Subtype.ext
  exact congrArg (Polynomial.monomial n) he

theorem objectPolynomial_scissor (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ)
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectPolynomial h00 hκ hs B hr hγ k n (I ∪ J) hU μ hμ + objectPolynomial h00 hκ hs B hr hγ k n (I ∩ J) hN μ hμ =
      objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ + objectPolynomial h00 hκ hs B hr hγ k n J hJ μ hμ := by
  have he : profileCoefficient h00 hκ hs B hr hγ k (I ∪ J) hU μ hμ +
      profileCoefficient h00 hκ hs B hr hγ k (I ∩ J) hN μ hμ =
      profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ + profileCoefficient h00 hκ hs B hr hγ k J hJ μ hμ := by
    apply Subtype.ext
    exact congrArg Subtype.val (profile_scissor h00 hκ hs B hr hγ k I J hI hJ hU hN μ hμ)
  apply Subtype.ext
  change Polynomial.monomial n _ + Polynomial.monomial n _ = Polynomial.monomial n _ + Polynomial.monomial n _
  simpa only [map_add] using congrArg (Polynomial.monomial n) he

theorem objectPolynomial_empty (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (hE : GammaDefinable B (∅ : Set (Fin n → Values.Gamma (M := M))))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    objectPolynomial h00 hκ hs B hr hγ k n ∅ hE μ hμ = 0 := by
  have he : profileCoefficient h00 hκ hs B hr hγ k ∅ hE μ hμ = 0 := by
    apply Subtype.ext
    exact congrArg Subtype.val (profile_empty h00 hκ hs B hr hγ k hE μ hμ)
  apply Subtype.ext
  change Polynomial.monomial n _ = 0
  rw [he, Polynomial.monomial_zero_right]

theorem objectPolynomial_eq_on_domain (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ ν : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : MapDefinable B μ) (hν : MapDefinable B ν) (he : ∀ u ∈ I, μ u = ν u) :
    objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ = objectPolynomial h00 hκ hs B hr hγ k n I hI ν hν := by
  have hc : profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ =
      profileCoefficient h00 hκ hs B hr hγ k I hI ν hν := by
    apply Subtype.ext
    exact congrArg Subtype.val (profile_eq_on_domain h00 hκ hs B hr hγ k I hI μ ν hμ hν he)
  apply Subtype.ext
  exact congrArg (Polynomial.monomial n) hc

end DiamondIntegral.Section4.GammaObjectRelations
