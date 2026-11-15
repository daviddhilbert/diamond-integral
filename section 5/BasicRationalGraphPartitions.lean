import «section 5».RationalSpectrumGraphs
import «section 5».SubordinateConstructiblePartitions

/-! A definable bijection graph has a finite disjoint basic scheme
partition with one fixed forward and inverse rational description on
every piece. Coverage holds for all scheme points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language Topology
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

theorem complex_bijection_basic_rational_graph_partition {n m : ℕ}
    (G : Set (Fin n ⊕ Fin m → ℂ))
    (hG : (Set.univ : Set ℂ).Definable Language.ring G)
    (hu : ∀ (x : Fin n → ℂ) (y z : Fin m → ℂ),
      Sum.elim x y ∈ G → Sum.elim x z ∈ G → y = z)
    (hv : ∀ (y : Fin m → ℂ) (x z : Fin n → ℂ),
      Sum.elim x y ∈ G → Sum.elim z y ∈ G → x = z) :
    ∃ Z : Set (PrimeSpectrum (MvPolynomial (Fin n ⊕ Fin m) ℂ)),
      IsConstructible Z ∧ (∀ v, v ∈ G ↔ complexTupleSpectrumPoint v ∈ Z) ∧
      ∃ (J : Type) (_ : Fintype J)
        (D : J → PrimeSpectrum.BasicConstructibleSetData (MvPolynomial (Fin n ⊕ Fin m) ℂ))
        (r : J → (Fin m → MvPolynomial (Fin n) ℂ) × MvPolynomial (Fin n) ℂ)
        (s : J → (Fin n → MvPolynomial (Fin m) ℂ) × MvPolynomial (Fin m) ℂ),
        (∀ j, (D j).toSet ⊆ Z ∩
          ((rationalSpectrumGraphData (r j).1 (r j).2).toSet ∩
            (inverseRationalSpectrumGraphData (s j).1 (s j).2).toSet)) ∧
        ∀ x, x ∈ Z ↔ ∃! j, x ∈ (D j).toSet := by
  obtain ⟨Z, hZ, heZ⟩ := complex_definable_finite_spectrum_constructible G hG
  obtain ⟨s, t, hst⟩ := complex_definable_bijection_finite_rational_cover G hG hu hv
  let I := ↥s × ↥t
  let C : I → Set (PrimeSpectrum (MvPolynomial (Fin n ⊕ Fin m) ℂ)) := fun i =>
    (rationalSpectrumGraphData i.1.val.1 i.1.val.2).toSet ∩
      (inverseRationalSpectrumGraphData i.2.val.1 i.2.val.2).toSet
  have hC (i : I) : IsConstructible (C i) :=
    (basicConstructibleData_isConstructible _).inter (basicConstructibleData_isConstructible _)
  have hpoint (φ : MvPolynomial (Fin n ⊕ Fin m) ℂ →ₐ[ℂ] ℂ)
      (hφ : complexAlgebraPoint φ ∈ Z) : ∃ i, complexAlgebraPoint φ ∈ C i := by
    let x : Fin n → ℂ := fun i => φ (MvPolynomial.X (.inl i))
    let y : Fin m → ℂ := fun j => φ (MvPolynomial.X (.inr j))
    have htuple : complexTupleSpectrumPoint (Sum.elim x y) = complexAlgebraPoint φ := by
      have he : Sum.elim x y = (fun i => φ (MvPolynomial.X i)) := by
        funext i
        cases i <;> rfl
      rw [he]
      exact complexTupleSpectrumPoint_algHom φ
    have hxy : Sum.elim x y ∈ G := (heZ _).mpr (htuple.symm ▸ hφ)
    obtain ⟨r, hr, u, hu, hforward, hinverse⟩ := hst x y hxy
    refine ⟨(⟨r, hr⟩, ⟨u, hu⟩), ?_⟩
    change complexAlgebraPoint φ ∈ (rationalSpectrumGraphData r.1 r.2).toSet ∩
      (inverseRationalSpectrumGraphData u.1 u.2).toSet
    rw [← htuple]
    exact ⟨(rationalSpectrumGraphData_point r.1 r.2 _).mpr hforward,
      (inverseRationalSpectrumGraphData_point u.1 u.2 x y).mpr hinverse⟩
  have hfull (x : PrimeSpectrum (MvPolynomial (Fin n ⊕ Fin m) ℂ)) (hx : x ∈ Z) :
      ∃ i, x ∈ C i := by
    by_contra hn
    let U := ⋃ i, C i
    have hU : IsConstructible U := IsConstructible.iUnion hC
    have hnx : x ∉ U := by simpa only [U, Set.mem_iUnion] using hn
    obtain ⟨φ, hφ⟩ := constructible_complex_point (Z \ U) (hZ.sdiff hU) ⟨x, hx, hnx⟩
    obtain ⟨i, hi⟩ := hpoint φ hφ.1
    exact hφ.2 (Set.mem_iUnion.mpr ⟨i, hi⟩)
  obtain ⟨J, hJ, D, select, hsub, hpartition⟩ := finite_subordinate_basic_partition Z hZ C hC hfull
  exact ⟨Z, hZ, heZ, J, hJ, D, (fun j => (select j).1.val), (fun j => (select j).2.val),
    hsub, hpartition⟩

end DiamondIntegral.Section5
