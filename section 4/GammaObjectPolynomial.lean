import «section 4».GammaZeroDegreeProfile

/-! An actual definable weighted Gamma set gives a homogeneous polynomial
in the manuscript's restricted source ring. This constructs the object
assignment; multiplicativity and category descent remain separate proofs. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaObjectPolynomial
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaZeroDegreeProfile
open GammaDefinableConvolution GammaPointAlgebra GammaFunctionPolynomial

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def profileCoefficient (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : baseSubring B k :=
  ⟨(profile h00 hκ hs B hr hγ k I hI μ hμ).val, (profile h00 hκ hs B hr hγ k I hI μ hμ).property⟩

theorem profile_monomial_mem (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    Polynomial.monomial n (profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ) ∈ sourceRing B k := by
  by_cases hn : n = 0
  · subst n
    rw [Polynomial.monomial_zero_left, C_mem_sourceRing]
    exact profile_zero_degree_pointSubring h00 hκ hs B hr hγ k I hI μ hμ
  · exact monomial_mem_sourceRing B k n hn _

def objectPolynomial (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) : sourceRing B k :=
  ⟨Polynomial.monomial n (profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ),
    profile_monomial_mem h00 hκ hs B hr hγ k n I hI μ hμ⟩

theorem objectPolynomial_coeff (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) (j : ℕ) :
    (objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ).val.coeff j =
      if n = j then profileCoefficient h00 hκ hs B hr hγ k I hI μ hμ else 0 :=
  Polynomial.coeff_monomial

end DiamondIntegral.Section4.GammaObjectPolynomial
