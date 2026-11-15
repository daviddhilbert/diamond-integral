import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Clopen
import Mathlib.Data.Finset.Card

/-! A finite closed family gives locally closed strata by counting
membership. Each generator becomes clopen on a stratum. This construction
is compatible with permutations of the closed family. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical Set Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]

def closedFamilySupport (C : ι → Set X) (s : Finset ι) (x : X) : Finset ι :=
  s.filter (fun i => x ∈ C i)

def closedFamilyDepth (C : ι → Set X) (x : X) : ℕ :=
  (closedFamilySupport C Finset.univ x).card

def closedFamilyAtLeast (C : ι → Set X) (s : Finset ι) (k : ℕ) : Set X :=
  ⋃ t : {t : Finset ι // t ⊆ s ∧ k ≤ t.card}, ⋂ i ∈ t.val, C i

theorem mem_closedFamilyAtLeast (C : ι → Set X) (s : Finset ι) (k : ℕ) (x : X) :
    x ∈ closedFamilyAtLeast C s k ↔ k ≤ (closedFamilySupport C s x).card := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
    apply t.property.2.trans (Finset.card_le_card ?_)
    intro i hi
    exact Finset.mem_filter.mpr ⟨t.property.1 hi,
      Set.mem_iInter.mp (Set.mem_iInter.mp ht i) hi⟩
  · intro hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨closedFamilySupport C s x, Finset.filter_subset _ _, hx⟩, ?_⟩
    apply Set.mem_iInter.mpr
    intro i
    apply Set.mem_iInter.mpr
    intro hi
    exact (Finset.mem_filter.mp hi).2

theorem closedFamilyAtLeast_isClosed (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (s : Finset ι) (k : ℕ) : IsClosed (closedFamilyAtLeast C s k) := by
  apply isClosed_iUnion_of_finite
  intro t
  exact isClosed_biInter (fun i _ => hC i)

def closedFamilyStratum (C : ι → Set X) (k : ℕ) : Set X :=
  {x | closedFamilyDepth C x = k}

theorem closedFamilyStratum_eq (C : ι → Set X) (k : ℕ) :
    closedFamilyStratum C k =
      (closedFamilyAtLeast C Finset.univ (k + 1))ᶜ ∩ closedFamilyAtLeast C Finset.univ k := by
  ext x
  simp only [closedFamilyStratum, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    mem_closedFamilyAtLeast, closedFamilyDepth]
  omega

theorem closedFamilyStratum_isLocallyClosed (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (k : ℕ) : IsLocallyClosed (closedFamilyStratum C k) := by
  rw [closedFamilyStratum_eq]
  exact ⟨_, _, (closedFamilyAtLeast_isClosed C hC _ _).isOpen_compl,
    closedFamilyAtLeast_isClosed C hC _ _, rfl⟩

theorem closedFamilySupport_erase (C : ι → Set X) (x : X) (i : ι) :
    closedFamilySupport C (Finset.univ.erase i) x =
      (closedFamilySupport C Finset.univ x).erase i := by
  ext j
  simp [closedFamilySupport, and_left_comm]

theorem closedFamilyStratum_generator_compl (C : ι → Set X) (k : ℕ) (i : ι)
    (x : closedFamilyStratum C k) :
    x.val ∉ C i ↔ x.val ∈ closedFamilyAtLeast C (Finset.univ.erase i) k := by
  rw [mem_closedFamilyAtLeast, closedFamilySupport_erase]
  have hx : (closedFamilySupport C Finset.univ x.val).card = k := x.property
  by_cases hi : x.val ∈ C i
  · have hmem : i ∈ closedFamilySupport C Finset.univ x.val := by
      simp [closedFamilySupport, hi]
    rw [Finset.card_erase_of_mem hmem]
    have hp := Finset.card_pos.mpr ⟨i, hmem⟩
    simp only [hi, not_true_eq_false, false_iff]
    omega
  · have hmem : i ∉ closedFamilySupport C Finset.univ x.val := by
      simp [closedFamilySupport, hi]
    rw [Finset.erase_eq_of_notMem hmem, hx]
    simp [hi]

theorem closedFamilyStratum_generator_isClopen (C : ι → Set X)
    (hC : ∀ i, IsClosed (C i)) (k : ℕ) (i : ι) :
    IsClopen {x : closedFamilyStratum C k | x.val ∈ C i} := by
  constructor
  · exact (hC i).preimage continuous_subtype_val
  · have he : ({x : closedFamilyStratum C k | x.val ∈ C i} : Set (closedFamilyStratum C k))ᶜ =
        Subtype.val ⁻¹' closedFamilyAtLeast C (Finset.univ.erase i) k := by
      ext x
      exact closedFamilyStratum_generator_compl C k i x
    rw [← isClosed_compl_iff, he]
    exact (closedFamilyAtLeast_isClosed C hC _ _).preimage continuous_subtype_val

theorem closedFamilyStratum_unique (C : ι → Set X) (x : X) :
    ∃! k : Fin (Fintype.card ι + 1), x ∈ closedFamilyStratum C k.val := by
  have hb : closedFamilyDepth C x ≤ Fintype.card ι :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)
  refine ⟨⟨closedFamilyDepth C x, by omega⟩, rfl, ?_⟩
  intro k hk
  exact Fin.ext hk.symm

theorem closedFamilyDepth_permutation (C : ι → Set X) (e : ι ≃ ι) (x y : X)
    (he : ∀ i, x ∈ C i ↔ y ∈ C (e i)) : closedFamilyDepth C x = closedFamilyDepth C y := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simp only [closedFamilySupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (he i).mp hi
  · intro i hi j hj hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simp only [closedFamilySupport, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (he (e.symm j)).mpr (by simpa using hj)

end DiamondIntegral.Section5
