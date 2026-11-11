import «section 2».UniformBoundaryRepresentatives
import «section 2».BoundaryTagFibres

/-! The finite-valued representative correspondence in the main proof of
2.35. Each nonempty boundary contributes one point per tag; an empty
boundary contributes the singleton zero, exactly as in the manuscript. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def boundaryTagSet (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (a : Fin n → M) : Set (RVInfinity M) :=
  {t | Fin.snoc a t.val ∈ coordinateBoundaryPairs A i}

def boundaryRepresentativeCandidates (A : Set (Fin (n+1) → M)) (i : Fin (n+1))
    (f : (Fin (n+1) → M) → M) (a : Fin n → M) : Set M :=
  (fun t : RVInfinity M => f (Fin.snoc a t.val)) '' boundaryTagSet A i a

noncomputable def boundaryRepresentativeValues (A : Set (Fin (n+1) → M)) (i : Fin (n+1))
    (f : (Fin (n+1) → M) → M) (a : Fin n → M) : Set M := by
  classical
  exact if (boundaryRepresentativeCandidates A i f a).Nonempty then
    boundaryRepresentativeCandidates A i f a else {(0 : VF M).val}

theorem boundaryRepresentativeValues_finite (B : ParameterBase M)
    (A : Set (Fin (n+1) → M)) (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) A)
    (i : Fin (n+1)) (f : (Fin (n+1) → M) → M) (a : Fin n → M) (ha : ∀ j, iVF (a j)) :
    (boundaryRepresentativeValues A i f a).Finite := by
  classical
  have hfin : (boundaryRepresentativeCandidates A i f a).Finite :=
    (coordinateBoundaryPairs_finite_tags B A hA i a ha).image _
  unfold boundaryRepresentativeValues
  split_ifs
  · exact hfin
  · exact Set.finite_singleton _

theorem boundaryRepresentativeCandidates_rv_injective
    (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (f : (Fin (n+1) → M) → M)
    (hf : ∀ p ∈ coordinateBoundaryPairs A i, iVF (f p) ∧ iRv (f p) = p (Fin.last n)) (a : Fin n → M) :
    Set.InjOn iRv (boundaryRepresentativeCandidates A i f a) := by
  rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩ he
  have hfs := (hf _ hs).2
  have hft := (hf _ ht).2
  simp only [Fin.snoc_last] at hfs hft
  have hst : s = t := Subtype.ext (hfs.symm.trans (he.trans hft))
  subst t
  rfl

theorem boundaryRepresentativeValues_rv_injective
    (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (f : (Fin (n+1) → M) → M)
    (hf : ∀ p ∈ coordinateBoundaryPairs A i, iVF (f p) ∧ iRv (f p) = p (Fin.last n)) (a : Fin n → M) :
    Set.InjOn iRv (boundaryRepresentativeValues A i f a) := by
  classical
  unfold boundaryRepresentativeValues
  split_ifs
  · exact boundaryRepresentativeCandidates_rv_injective A i f hf a
  · intro x hx y hy _
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm

theorem boundaryRepresentativeValues_proper
    (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (f : (Fin (n+1) → M) → M)
    (hf : ∀ p ∈ coordinateBoundaryPairs A i, iVF (f p) ∧ iRv (f p) = p (Fin.last n)) (a : Fin n → M) :
    boundaryRepresentativeValues A i f a ⊆ {x | iVF x} := by
  classical
  unfold boundaryRepresentativeValues
  split_ifs
  · rintro _ ⟨t,ht,rfl⟩
    exact (hf _ ht).1
  · intro x hx
    have he : x = (0 : VF M).val := Set.mem_singleton_iff.mp hx
    exact he.symm ▸ (0 : VF M).property

theorem boundaryTagSet_subset_representative_rv_image
    (A : Set (Fin (n+1) → M)) (i : Fin (n+1)) (f : (Fin (n+1) → M) → M)
    (hf : ∀ p ∈ coordinateBoundaryPairs A i, iVF (f p) ∧ iRv (f p) = p (Fin.last n)) (a : Fin n → M) :
    Subtype.val '' boundaryTagSet A i a ⊆ iRv '' boundaryRepresentativeValues A i f a := by
  classical
  rintro _ ⟨t,ht,rfl⟩
  have hmem : f (Fin.snoc a t.val) ∈ boundaryRepresentativeCandidates A i f a := ⟨t,ht,rfl⟩
  have hne : (boundaryRepresentativeCandidates A i f a).Nonempty := ⟨_,hmem⟩
  refine ⟨f (Fin.snoc a t.val),?_,?_⟩
  · simpa only [boundaryRepresentativeValues,ite_eq_left hne] using hmem
  · simpa only [Fin.snoc_last] using (hf _ ht).2

end DiamondIntegral.Section2
