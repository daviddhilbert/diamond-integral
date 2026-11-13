import «section 4».RestrictedPolynomialGrading
import «section 4».GammaBoundedObjectPolynomial

/-! Both actual Gamma polynomial sources have their natural grading with
the required degree-zero restriction. The bounded inclusion preserves it,
and actual Gamma object polynomials have their stated degree. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPolynomialGradings
open GammaDefinableConvolution GammaBoundedFunctions
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def unboundedPiece (B : Base (M := M)) (k : EulerKind) (n : ℕ) :
    AddSubgroup (GammaFunctionPolynomial.sourceRing B k) :=
  RestrictedPolynomialGrading.piece (GammaPointAlgebra.pointSubring B k) n

instance unboundedGradedRing (B : Base (M := M)) (k : EulerKind) : GradedRing (unboundedPiece B k) :=
  RestrictedPolynomialGrading.gradedRing _

theorem mem_unboundedPiece (B : Base (M := M)) (k : EulerKind)
    (p : GammaFunctionPolynomial.sourceRing B k) (n : ℕ) :
    p ∈ unboundedPiece B k n ↔ p.val = Polynomial.monomial n (p.val.coeff n) :=
  RestrictedPolynomialGrading.mem_piece _ p n

theorem unbounded_monomial_mem (B : Base (M := M)) (k : EulerKind)
    (p : GammaFunctionPolynomial.sourceRing B k) (n : ℕ) (f : baseSubring B k)
    (hp : p.val = Polynomial.monomial n f) : p ∈ unboundedPiece B k n := by
  rw [mem_unboundedPiece, hp, Polynomial.coeff_monomial_same]

def boundedPiece (B : Base (M := M)) (k : EulerKind) (n : ℕ) :
    AddSubgroup (GammaBoundedPolynomial.sourceRing B k) :=
  RestrictedPolynomialGrading.piece (GammaBoundedPolynomial.boundedPointSubring B k) n

instance boundedGradedRing (B : Base (M := M)) (k : EulerKind) : GradedRing (boundedPiece B k) :=
  RestrictedPolynomialGrading.gradedRing _

theorem mem_boundedPiece (B : Base (M := M)) (k : EulerKind)
    (p : GammaBoundedPolynomial.sourceRing B k) (n : ℕ) :
    p ∈ boundedPiece B k n ↔ p.val = Polynomial.monomial n (p.val.coeff n) :=
  RestrictedPolynomialGrading.mem_piece _ p n

theorem bounded_monomial_mem (B : Base (M := M)) (k : EulerKind)
    (p : GammaBoundedPolynomial.sourceRing B k) (n : ℕ) (f : boundedBaseSubring B k)
    (hp : p.val = Polynomial.monomial n f) : p ∈ boundedPiece B k n := by
  rw [mem_boundedPiece, hp, Polynomial.coeff_monomial_same]

theorem toUnbounded_mem (B : Base (M := M)) (k : EulerKind) {n : ℕ}
    {p : GammaBoundedPolynomial.sourceRing B k} (hp : p ∈ boundedPiece B k n) :
    GammaBoundedPolynomial.toUnbounded B k p ∈ unboundedPiece B k n := by
  have he := (mem_boundedPiece B k p n).mp hp
  apply unbounded_monomial_mem B k _ n (GammaBoundedPolynomial.forgetBounded B k (p.val.coeff n))
  change p.val.map (GammaBoundedPolynomial.forgetBounded B k) = _
  rw [he, Polynomial.map_monomial, Polynomial.coeff_monomial_same]

theorem objectPolynomial_mem (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n : ℕ) (I : Set (Fin n → Values.Gamma (M := M)))
    (hI : GammaOrderLogic.GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : GammaDefinableMaps.MapDefinable B μ) :
    GammaObjectPolynomial.objectPolynomial h00 hκ hs B hr hγ k n I hI μ hμ ∈ unboundedPiece B k n :=
  unbounded_monomial_mem B k _ n _ rfl

theorem boundedObjectPolynomial_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaOrderLogic.GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : GammaDefinableMaps.MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    GammaBoundedObjectPolynomial.objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k n I hI μ hμ hbox ∈
      boundedPiece B k n := bounded_monomial_mem B k _ n _ rfl

end DiamondIntegral.Section4.GammaPolynomialGradings
