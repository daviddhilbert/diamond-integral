import «section 4».GammaBoundedPolynomial
import «section 4».GammaBoundedProfileRange
import «section 4».GammaZeroDegreeProfile
import «section 4».GammaObjectPolynomial

/-! Actual bounded weighted Gamma sets give homogeneous polynomials in
the bounded restricted source. Forgetting boundedness recovers the proved
unbounded assignment; coefficientwise Euler evaluation gives chi(I) X^n. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedObjectPolynomial
open GammaOrderLogic GammaDefinableMaps GammaBoundedPolynomial GammaBoundedProfileRange GammaBoundedFunctions
open GammaIntegerFamilies GammaIndicators GammaIteratedIntegral GammaPointAlgebra

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def objectPolynomial (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) : sourceRing B k := by
  refine ⟨Polynomial.monomial n (boundedProfile hc h00 linear hκ hs B hr hγ hΓ k I hI μ hμ hbox), ?_⟩
  rw [mem_sourceRing, Polynomial.coeff_monomial]
  by_cases hn : n = 0
  · subst n
    rw [ite_eq_left rfl]
    exact GammaZeroDegreeProfile.profile_zero_degree_pointSubring h00 hκ hs B hr hγ k I hI μ hμ
  · rw [ite_eq_right hn, map_zero]
    exact (pointSubring B k).zero_mem

theorem toUnbounded_objectPolynomial (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    toUnbounded B k (objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k n I hI μ hμ hbox) =
      GammaObjectPolynomial.objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ := by
  apply Subtype.ext
  change Polynomial.map (forgetBounded B k) (Polynomial.monomial n _) = Polynomial.monomial n _
  rw [Polynomial.map_monomial]
  rfl

def eulerPolynomial (B : Base (M := M)) (k : EulerKind) : sourceRing B k →+* Polynomial ℤ :=
  (Polynomial.mapRingHom (baseBoundedEuler B k)).comp (sourceRing B k).subtype

theorem eulerPolynomial_object (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    eulerPolynomial B k (objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k n I hI μ hμ hbox) =
      Polynomial.monomial n (integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B I hI)) := by
  change Polynomial.map (baseBoundedEuler B k) (Polynomial.monomial n _) = _
  rw [Polynomial.map_monomial, boundedProfile_euler]

end DiamondIntegral.Section4.GammaBoundedObjectPolynomial
