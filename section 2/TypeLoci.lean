import «section 2».TypeLocalCompactness
import «section 2».Atomic
import Section3.ParameterBridge

/-! Actual complete type loci over a real ground base. The sortedness and
maximality needed by the manuscript's Definition 2.22 are proved here. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rawTypeLocus_generates (S : Set M) {n : ℕ} (sn : Fin n → SortTag)
    (a : Fin n → M) (ha : a ∈ GammaParameters.sortedUniverse sn) :
    GeneratesCompleteType ⟨S,∅⟩ sn (rawTypeLocus S a) := by
  refine ⟨⟨a,mem_rawTypeLocus S a⟩,?_,?_⟩
  · exact fun _ hx => hx _ (GammaParameters.sortedUniverse_definable S sn).raw_definable ha
  · intro C hC
    exact rawTypeLocus_decides a C ((GammaParameters.base_empty_iff S sn C).mp hC).raw_definable

theorem rawTypeLocus_complete
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) {n : ℕ}
    (sn : Fin n → SortTag) (a : Fin n → M)
    (ha : a ∈ GammaParameters.sortedUniverse sn) :
    IsCompleteTypeDefinable ⟨S,∅⟩ sn (rawTypeLocus S a) := by
  refine ⟨rawTypeLocus_generates S sn a ha,?_⟩
  intro C hsub hC x hx U hU haU
  have hUs : DefinableOver S sn (U ∩ GammaParameters.sortedUniverse sn) :=
    raw_definableOver_sorted hc S sn _
      (hU.inter (GammaParameters.sortedUniverse_definable S sn).raw_definable)
      Set.inter_subset_right
  rcases hC.2.2 _ ((GammaParameters.base_empty_iff S sn _).mpr hUs) with h | h
  · exact (h hx).1
  · exact (Set.disjoint_left.mp h (hsub (mem_rawTypeLocus S a)) ⟨haU,ha⟩).elim

end DiamondIntegral.Section2
