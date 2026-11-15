import «section 5».ComplexSpectrumConstructibility
import «section 5».RationalGraphBijections
import «section 5».ComplexConstructiblePoints

/-! Rational matching loci as actual basic constructible subsets of
the graph spectrum, with exact original complex-point semantics. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Topology

def rationalSpectrumGraphData {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ) where
  f := MvPolynomial.rename Sum.inl q
  n := m
  g j := MvPolynomial.X (Sum.inr j) * MvPolynomial.rename Sum.inl q - MvPolynomial.rename Sum.inl (p j)

theorem basicConstructibleData_isConstructible {A : Type*} [CommRing A]
    (D : PrimeSpectrum.BasicConstructibleSetData A) : IsConstructible D.toSet := by
  have h := ({D} : PrimeSpectrum.ConstructibleSetData A).isConstructible_toSet
  simpa [PrimeSpectrum.ConstructibleSetData.toSet] using h

theorem rationalSpectrumGraphData_point {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (v : Fin n ⊕ Fin m → ℂ) :
    complexTupleSpectrumPoint v ∈ (rationalSpectrumGraphData p q).toSet ↔
      v ∈ rationalTupleEquationSet p q := by
  simp [rationalSpectrumGraphData, PrimeSpectrum.BasicConstructibleSetData.toSet,
    complexTupleSpectrumPoint, PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff,
    RingHom.mem_ker, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename,
    rationalTupleEquationSet, Function.comp_def, and_comm, sub_eq_zero]

theorem complexTupleSpectrumPoint_algHom {α : Type} (φ : MvPolynomial α ℂ →ₐ[ℂ] ℂ) :
    complexTupleSpectrumPoint (fun i => φ (MvPolynomial.X i)) = complexAlgebraPoint φ := by
  have he : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) = φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  apply PrimeSpectrum.ext
  change RingHom.ker (MvPolynomial.aeval (fun i => φ (MvPolynomial.X i))).toRingHom =
    RingHom.ker φ.toRingHom
  rw [he]

def inverseRationalSpectrumGraphData {n m : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℂ) (q : MvPolynomial (Fin m) ℂ) :
    PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ) :=
  (rationalSpectrumGraphData p q).map (MvPolynomial.rename Sum.swap).toRingHom

theorem inverseRationalSpectrumGraphData_denominator {n m : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℂ) (q : MvPolynomial (Fin m) ℂ) :
    (inverseRationalSpectrumGraphData p q).f = MvPolynomial.rename Sum.inr q := by
  change MvPolynomial.rename Sum.swap (MvPolynomial.rename Sum.inl q) = _
  rw [MvPolynomial.rename_rename]
  rfl

theorem inverseRationalSpectrumGraphData_equation {n m : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℂ) (q : MvPolynomial (Fin m) ℂ) (i : Fin n) :
    (inverseRationalSpectrumGraphData p q).g i =
      MvPolynomial.X (.inl i) * MvPolynomial.rename Sum.inr q - MvPolynomial.rename Sum.inr (p i) := by
  simp only [inverseRationalSpectrumGraphData, PrimeSpectrum.BasicConstructibleSetData.map,
    rationalSpectrumGraphData, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_sub, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_rename]
  rfl

theorem inverseRationalSpectrumGraphData_point {n m : ℕ}
    (p : Fin n → MvPolynomial (Fin m) ℂ) (q : MvPolynomial (Fin m) ℂ)
    (x : Fin n → ℂ) (y : Fin m → ℂ) :
    complexTupleSpectrumPoint (Sum.elim x y) ∈ (inverseRationalSpectrumGraphData p q).toSet ↔
      Sum.elim y x ∈ rationalTupleEquationSet p q := by
  rw [inverseRationalSpectrumGraphData, PrimeSpectrum.BasicConstructibleSetData.toSet_map]
  simp only [Set.mem_preimage]
  have hv : Sum.elim x y ∘ Sum.swap = Sum.elim y x := by
    funext i
    cases i <;> rfl
  have he : PrimeSpectrum.comap (MvPolynomial.rename Sum.swap).toRingHom
      (complexTupleSpectrumPoint (Sum.elim x y)) = complexTupleSpectrumPoint (Sum.elim y x) := by
    ext P
    simp [complexTupleSpectrumPoint, RingHom.mem_ker, MvPolynomial.eval₂_rename, hv]
  rw [he]
  exact rationalSpectrumGraphData_point p q _

end DiamondIntegral.Section5
