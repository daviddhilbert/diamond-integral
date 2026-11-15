import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Ideal.Operations

/-! A finite family of polynomial tests partitions a prime spectrum
into disjoint basic constructible atoms. The negative tests are combined
into one nonvanishing product. Empty families are included. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
open scoped BigOperators
variable {A : Type*} [CommRing A]

def primeSignSupport (P : Finset A) (x : PrimeSpectrum A) : Finset A :=
  P.filter (fun a => a ∈ x.asIdeal)

def primeSignAtomData (P T : Finset A) : PrimeSpectrum.BasicConstructibleSetData A where
  f := ∏ a ∈ P \ T, a
  n := Fintype.card T
  g i := ((Fintype.equivFin T).symm i).val

theorem primeSignAtomData_range (P T : Finset A) :
    Set.range (primeSignAtomData P T).g = (T : Set A) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Fintype.equivFin T).symm i).property
  · intro ha
    refine ⟨(Fintype.equivFin T) ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val ((Fintype.equivFin T).symm_apply_apply ⟨a, ha⟩)

theorem primeSignAtomData_mem (P T : Finset A) (hT : T ⊆ P) (x : PrimeSpectrum A) :
    x ∈ (primeSignAtomData P T).toSet ↔ ∀ a ∈ P, (a ∈ x.asIdeal ↔ a ∈ T) := by
  have hn : (∏ a ∈ P \ T, a) ∉ x.asIdeal ↔ ∀ a ∈ P \ T, a ∉ x.asIdeal := by
    rw [x.isPrime.prod_mem_iff_exists_mem]
    push_neg
    rfl
  have he : x ∈ (primeSignAtomData P T).toSet ↔
      (∀ a ∈ T, a ∈ x.asIdeal) ∧ ∀ a ∈ P \ T, a ∉ x.asIdeal := by
    change (Set.range (primeSignAtomData P T).g ⊆ (x.asIdeal : Set A)) ∧
      ¬ ({∏ a ∈ P \ T, a} : Set A) ⊆ (x.asIdeal : Set A) ↔ _
    rw [primeSignAtomData_range, Set.singleton_subset_iff]
    exact and_congr Iff.rfl hn
  rw [he]
  constructor
  · rintro ⟨hpos, hneg⟩ a ha
    constructor
    · intro hx
      by_contra ht
      exact hneg a (Finset.mem_sdiff.mpr ⟨ha, ht⟩) hx
    · exact hpos a
  · intro h
    constructor
    · intro a ha
      exact (h a (hT ha)).mpr ha
    · intro a ha hx
      exact (Finset.mem_sdiff.mp ha).2 ((h a (Finset.mem_sdiff.mp ha).1).mp hx)

theorem primeSignAtomData_support (P T : Finset A) (hT : T ⊆ P) (x : PrimeSpectrum A) :
    x ∈ (primeSignAtomData P T).toSet ↔ primeSignSupport P x = T := by
  rw [primeSignAtomData_mem P T hT]
  constructor
  · intro h
    ext a
    constructor
    · intro ha
      exact (h a (Finset.mem_filter.mp ha).1).mp (Finset.mem_filter.mp ha).2
    · intro ha
      exact Finset.mem_filter.mpr ⟨hT ha, (h a (hT ha)).mpr ha⟩
  · intro he a ha
    have h := Finset.ext_iff.mp he a
    simpa only [primeSignSupport, Finset.mem_filter, ha, true_and] using h

theorem primeSignAtoms_unique (P : Finset A) (x : PrimeSpectrum A) :
    ∃! T : ↥P.powerset, x ∈ (primeSignAtomData P T.val).toSet := by
  let T := primeSignSupport P x
  have hT : T ⊆ P := Finset.filter_subset _ _
  refine ⟨⟨T, Finset.mem_powerset.mpr hT⟩,
    (primeSignAtomData_support P T hT x).mpr rfl, ?_⟩
  intro U hU
  apply Subtype.ext
  exact ((primeSignAtomData_support P U.val (Finset.mem_powerset.mp U.property) x).mp hU).symm

end DiamondIntegral.Section5
