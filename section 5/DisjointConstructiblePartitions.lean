import «section 5».PrimeSignAtoms

/-! Every constructible subset of an affine spectrum has a finite
disjoint partition by basic constructible subsets. The pieces are
explicit sign atoms of a finite list of ring elements. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Topology
universe u
variable {A : Type u} [CommRing A]

def constructibleTestPolynomials (S : PrimeSpectrum.ConstructibleSetData A) : Finset A :=
  S.biUnion (fun D => insert D.f (Finset.univ.image D.g))

theorem constructibleTestPolynomials_denominator (S : PrimeSpectrum.ConstructibleSetData A)
    (D : PrimeSpectrum.BasicConstructibleSetData A) (hD : D ∈ S) :
    D.f ∈ constructibleTestPolynomials S :=
  Finset.mem_biUnion.mpr ⟨D, hD, Finset.mem_insert_self _ _⟩

theorem constructibleTestPolynomials_equation (S : PrimeSpectrum.ConstructibleSetData A)
    (D : PrimeSpectrum.BasicConstructibleSetData A) (hD : D ∈ S) (i : Fin D.n) :
    D.g i ∈ constructibleTestPolynomials S :=
  Finset.mem_biUnion.mpr ⟨D, hD, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

theorem primeSignSupport_test (P : Finset A) (x y : PrimeSpectrum A)
    (he : primeSignSupport P x = primeSignSupport P y) (a : A) (ha : a ∈ P) :
    a ∈ x.asIdeal ↔ a ∈ y.asIdeal := by
  have h := Finset.ext_iff.mp he a
  simpa only [primeSignSupport, Finset.mem_filter, ha, true_and] using h

theorem constructibleData_same_sign (S : PrimeSpectrum.ConstructibleSetData A)
    (x y : PrimeSpectrum A)
    (he : primeSignSupport (constructibleTestPolynomials S) x =
      primeSignSupport (constructibleTestPolynomials S) y) :
    x ∈ S.toSet ↔ y ∈ S.toSet := by
  have hd (D : PrimeSpectrum.BasicConstructibleSetData A) (hD : D ∈ S) :
      x ∈ D.toSet ↔ y ∈ D.toSet := by
    have hf := primeSignSupport_test _ x y he D.f (constructibleTestPolynomials_denominator S D hD)
    have hg (i : Fin D.n) := primeSignSupport_test _ x y he (D.g i)
      (constructibleTestPolynomials_equation S D hD i)
    simpa only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
      PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe] using
      and_congr (forall_congr' hg) (not_congr hf)
  constructor
  · intro hx
    obtain ⟨D, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hD, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨D, Set.mem_iUnion.mpr ⟨hD, (hd D hD).mp hx⟩⟩
  · intro hy
    obtain ⟨D, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hD, hy⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨D, Set.mem_iUnion.mpr ⟨hD, (hd D hD).mpr hy⟩⟩

theorem finite_disjoint_basic_constructible_partition (Z : Set (PrimeSpectrum A))
    (hZ : IsConstructible Z) :
    ∃ (ι : Type u) (_ : Fintype ι) (D : ι → PrimeSpectrum.BasicConstructibleSetData A),
      (∀ i, (D i).toSet ⊆ Z) ∧ ∀ x, x ∈ Z ↔ ∃! i, x ∈ (D i).toSet := by
  obtain ⟨S, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hZ
  let P := constructibleTestPolynomials S
  let I := {T : ↥P.powerset // ∃ x ∈ S.toSet, primeSignSupport P x = T.val}
  let D : I → PrimeSpectrum.BasicConstructibleSetData A := fun i => primeSignAtomData P i.val.val
  have hsub (i : I) : (D i).toSet ⊆ S.toSet := by
    obtain ⟨x, hx, hxT⟩ := i.property
    intro y hy
    have hyT : primeSignSupport P y = i.val.val :=
      (primeSignAtomData_support P i.val.val (Finset.mem_powerset.mp i.val.property) y).mp hy
    exact (constructibleData_same_sign S x y (hxT.trans hyT.symm)).mp hx
  refine ⟨I, inferInstance, D, hsub, ?_⟩
  intro x
  constructor
  · intro hx
    let T : ↥P.powerset := ⟨primeSignSupport P x, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
    let i : I := ⟨T, x, hx, rfl⟩
    refine ⟨i, (primeSignAtomData_support P T.val (Finset.mem_powerset.mp T.property) x).mpr rfl, ?_⟩
    intro j hj
    apply Subtype.ext
    apply Subtype.ext
    exact ((primeSignAtomData_support P j.val.val (Finset.mem_powerset.mp j.val.property) x).mp hj).symm
  · rintro ⟨i, hi, _⟩
    exact hsub i hi

end DiamondIntegral.Section5
