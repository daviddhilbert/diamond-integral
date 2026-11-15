import «section 5».DisjointConstructiblePartitions

/-! Finite disjoint basic constructible partitions subordinate to a
specified finite constructible cover. Thus every piece keeps one fixed
rational-description branch when this is applied to a graph. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Topology
universe u
variable {A : Type u} [CommRing A]

theorem primeSignSupport_restrict (P Q : Finset A) (hQP : Q ⊆ P) (x y : PrimeSpectrum A)
    (he : primeSignSupport P x = primeSignSupport P y) : primeSignSupport Q x = primeSignSupport Q y := by
  ext a
  by_cases ha : a ∈ Q
  · simpa only [primeSignSupport, Finset.mem_filter, ha, true_and] using
      primeSignSupport_test P x y he a (hQP ha)
  · simp [primeSignSupport, ha]

theorem finite_constructible_test_family {ι : Type*} [Fintype ι]
    (Z : ι → Set (PrimeSpectrum A)) (hZ : ∀ i, IsConstructible (Z i)) :
    ∃ P : Finset A, ∀ i (x y : PrimeSpectrum A), primeSignSupport P x = primeSignSupport P y →
      (x ∈ Z i ↔ y ∈ Z i) := by
  choose S hS using (fun i => PrimeSpectrum.exists_constructibleSetData_iff.mpr (hZ i))
  let allData := Finset.univ.biUnion S
  let P := constructibleTestPolynomials allData
  have hsub (i : ι) : constructibleTestPolynomials (S i) ⊆ P := by
    intro a ha
    obtain ⟨D, hD, ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨D, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hD⟩, ha⟩
  refine ⟨P, ?_⟩
  intro i x y he
  rw [← hS i]
  exact constructibleData_same_sign (S i) x y (primeSignSupport_restrict P _ (hsub i) x y he)

theorem finite_subordinate_basic_partition {ι : Type*} [Fintype ι]
    (Z : Set (PrimeSpectrum A)) (hZ : IsConstructible Z)
    (C : ι → Set (PrimeSpectrum A)) (hC : ∀ i, IsConstructible (C i))
    (hcover : ∀ x ∈ Z, ∃ i, x ∈ C i) :
    ∃ (J : Type u) (_ : Fintype J) (D : J → PrimeSpectrum.BasicConstructibleSetData A)
      (select : J → ι),
      (∀ j, (D j).toSet ⊆ Z ∩ C (select j)) ∧
      ∀ x, x ∈ Z ↔ ∃! j, x ∈ (D j).toSet := by
  let F : Option ι → Set (PrimeSpectrum A) := fun i => i.elim Z C
  have hF (i : Option ι) : IsConstructible (F i) := by
    cases i with
    | none => exact hZ
    | some i => exact hC i
  obtain ⟨P, hsame⟩ := finite_constructible_test_family F hF
  let J := {T : ↥P.powerset // ∃ x ∈ Z, primeSignSupport P x = T.val}
  let D : J → PrimeSpectrum.BasicConstructibleSetData A := fun j => primeSignAtomData P j.val.val
  let w (j : J) : PrimeSpectrum A := Classical.choose j.property
  have hw (j : J) : w j ∈ Z ∧ primeSignSupport P (w j) = j.val.val := Classical.choose_spec j.property
  let select (j : J) : ι := Classical.choose (hcover (w j) (hw j).1)
  have hselect (j : J) : w j ∈ C (select j) := Classical.choose_spec (hcover (w j) (hw j).1)
  have hsub (j : J) : (D j).toSet ⊆ Z ∩ C (select j) := by
    intro x hx
    have hpx : primeSignSupport P x = j.val.val :=
      (primeSignAtomData_support P j.val.val (Finset.mem_powerset.mp j.val.property) x).mp hx
    have he := (hw j).2.trans hpx.symm
    exact ⟨(hsame none (w j) x he).mp (hw j).1,
      (hsame (some (select j)) (w j) x he).mp (hselect j)⟩
  refine ⟨J, inferInstance, D, select, hsub, ?_⟩
  intro x
  constructor
  · intro hx
    let T : ↥P.powerset := ⟨primeSignSupport P x, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
    let j : J := ⟨T, x, hx, rfl⟩
    refine ⟨j, (primeSignAtomData_support P T.val (Finset.mem_powerset.mp T.property) x).mpr rfl, ?_⟩
    intro k hk
    apply Subtype.ext
    apply Subtype.ext
    exact ((primeSignAtomData_support P k.val.val (Finset.mem_powerset.mp k.val.property) x).mp hk).symm
  · rintro ⟨j, hj, _⟩
    exact (hsub j hj).1

end DiamondIntegral.Section5
