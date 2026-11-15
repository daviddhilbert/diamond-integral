import «section 5».ComplexZariskiConstructibility
import «section 5».PrincipalRationalMaps

/-! The original rational expressions are continuous for the actual
Zariski topology on their principal domains. The proof uses the checked
scheme map and its evaluation-kernel square. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Topology TopologicalSpace
open SpecialTransformations.Section7
attribute [local instance] complexZariskiTopology

def complexPolynomialPoint {n : ℕ} (x : Fin n → ℂ) : PrimeSpectrum (MvPolynomial (Fin n) ℂ) :=
  ⟨RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ) x), RingHom.ker_isPrime _⟩

theorem complexPolynomialPoint_isInducing (n : ℕ) :
    IsInducing (complexPolynomialPoint : (Fin n → ℂ) → _) := by
  let f : MvPolynomial (Fin n) (⊤ : Subfield ℂ) →+* MvPolynomial (Fin n) ℂ :=
    MvPolynomial.map (⊤ : Subfield ℂ).subtype
  have hf : Function.Surjective f := MvPolynomial.map_surjective _ (fun c => ⟨⟨c, by trivial⟩, rfl⟩)
  have he : PrimeSpectrum.comap f ∘ complexPolynomialPoint =
      (fieldTuplePrime (⊤ : Subfield ℂ) : (Fin n → ℂ) → _) := by
    funext x
    ext p
    simp [f, complexPolynomialPoint, fieldTuplePrime, RingHom.mem_ker,
      MvPolynomial.eval₂_map]
  apply (PrimeSpectrum.comap_isInducing_of_surjective _ _ hf).of_comp_iff.mp
  rw [he]
  exact complexZariskiPoint_isInducing n

def principalComplexPoint {n : ℕ} (q : MvPolynomial (Fin n) ℂ)
    (x : {x : Fin n → ℂ | q.eval₂ (RingHom.id ℂ) x ≠ 0}) :
    PrimeSpectrum (Localization.Away q) :=
  ⟨RingHom.ker (principalPointEvaluation q x.val x.property), RingHom.ker_isPrime _⟩

theorem principalComplexPoint_square {n : ℕ} (q : MvPolynomial (Fin n) ℂ)
    (x : {x : Fin n → ℂ | q.eval₂ (RingHom.id ℂ) x ≠ 0}) :
    PrimeSpectrum.comap (algebraMap _ _) (principalComplexPoint q x) =
      complexPolynomialPoint x.val := by
  ext p
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, principalComplexPoint,
    complexPolynomialPoint, RingHom.mem_ker, principalPointEvaluation_algebraMap]
  rfl

theorem principalComplexPoint_continuous {n : ℕ} (q : MvPolynomial (Fin n) ℂ) :
    Continuous (principalComplexPoint q) := by
  apply (PrimeSpectrum.localization_comap_isInducing (Localization.Away q) (Submonoid.powers q)).continuous_iff.mpr
  have he : PrimeSpectrum.comap (algebraMap _ _) ∘ principalComplexPoint q =
      complexPolynomialPoint ∘ Subtype.val := funext (principalComplexPoint_square q)
  rw [he]
  exact (complexPolynomialPoint_isInducing n).continuous.comp continuous_subtype_val

def principalRationalTuple {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ)
    (x : {x : Fin n → ℂ | q.eval₂ (RingHom.id ℂ) x ≠ 0}) : Fin m → ℂ :=
  fun j => (p j).eval₂ (RingHom.id ℂ) x.val / q.eval₂ (RingHom.id ℂ) x.val

theorem principalRationalTuple_square {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (x : {x : Fin n → ℂ | q.eval₂ (RingHom.id ℂ) x ≠ 0}) :
    PrimeSpectrum.comap (principalRationalAlgebraMap p q).toRingHom (principalComplexPoint q x) =
      complexPolynomialPoint (principalRationalTuple p q x) := by
  have he := principalRationalAlgebraMap_point p q x.val x.property
  apply PrimeSpectrum.ext
  change RingHom.ker ((principalPointEvaluation q x.val x.property).comp
      (principalRationalAlgebraMap p q).toRingHom) = _
  rw [he]
  rfl

theorem principalRationalTuple_continuous {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    Continuous (principalRationalTuple p q) := by
  apply (complexPolynomialPoint_isInducing m).continuous_iff.mpr
  have he : complexPolynomialPoint ∘ principalRationalTuple p q =
      PrimeSpectrum.comap (principalRationalAlgebraMap p q).toRingHom ∘ principalComplexPoint q :=
    (funext (principalRationalTuple_square p q)).symm
  rw [he]
  exact (PrimeSpectrum.continuous_comap _).comp (principalComplexPoint_continuous q)

end DiamondIntegral.Section5
