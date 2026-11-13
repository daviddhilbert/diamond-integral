import «section 4».GammaBoundedObjectPolynomial

/-! Actual specialization of the bounded restricted polynomial source.
Its point/interval assignments are T^n and -T^n, and its value on an actual
bounded weighted domain is chi(I) T^n. A RES ring can be substituted for the
target once its separate category construction is available. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedSpecialization
open GammaOrderLogic GammaDefinableMaps GammaBoundedPolynomial GammaBoundedObjectPolynomial GammaBoundedFunctions
open GammaIndicators GammaIteratedIntegral

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def specialize (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R] (T : R) : sourceRing B k →+* R :=
  (Polynomial.eval₂RingHom (Int.castRingHom R) T).comp (eulerPolynomial B k)

theorem specialize_monomial (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R] (T : R)
    (p : sourceRing B k) (n : ℕ) (f : boundedBaseSubring B k) (hp : p.val = Polynomial.monomial n f) :
    specialize B k T p = (baseBoundedEuler B k f : R) * T ^ n := by
  change Polynomial.eval₂ (Int.castRingHom R) T (Polynomial.map (baseBoundedEuler B k) p.val) = _
  rw [hp, Polynomial.map_monomial, Polynomial.eval₂_monomial]
  rfl

def pointMonomial (B : Base (M := M)) (k : EulerKind) (n : ℕ) (a : Name B) : sourceRing B k :=
  ⟨Polynomial.monomial n (basePoint B k a), point_monomial_mem B k n a⟩

def intervalMonomial (B : Base (M := M)) (k : EulerKind) (n : ℕ) (hn : n ≠ 0) (a : Name B) : sourceRing B k :=
  ⟨Polynomial.monomial n (baseInterval B k a), monomial_mem_positive B k n hn _⟩

theorem specialize_point (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R] (T : R)
    (n : ℕ) (a : Name B) : specialize B k T (pointMonomial B k n a) = T ^ n := by
  rw [specialize_monomial B k T _ n (basePoint B k a) rfl, baseBoundedEuler_point]
  simp

theorem specialize_interval (B : Base (M := M)) (k : EulerKind) {R : Type*} [CommRing R] (T : R)
    (n : ℕ) (hn : n ≠ 0) (a : Name B) : specialize B k T (intervalMonomial B k n hn a) = -(T ^ n) := by
  rw [specialize_monomial B k T _ n (baseInterval B k a) rfl, baseBoundedEuler_interval]
  simp

theorem specialize_object (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n : ℕ)
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β)
    {R : Type*} [CommRing R] (T : R) :
    specialize B k T (objectPolynomial hc h00 linear hκ hs B hr hγ hΓ k n I hI μ hμ hbox) =
      (integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B I hI) : R) * T ^ n := by
  change Polynomial.eval₂ (Int.castRingHom R) T (eulerPolynomial B k _) = _
  rw [eulerPolynomial_object, Polynomial.eval₂_monomial]
  rfl

end DiamondIntegral.Section4.GammaBoundedSpecialization
