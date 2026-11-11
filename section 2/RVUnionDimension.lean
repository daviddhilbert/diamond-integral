import «section 2».Dimension
import Section4.FullDimension
import Section4.VFRealFibres

/-!
# The RV-union principle for the manuscript's dimension

For a definable VF/RV family, forgetting the RV index cannot create full
VF-dimensional interior. A generic VF tuple in an open projected box stays
independent after naming its RV index, and QE gives interior in that fibre.
This uses the section's direct interior-based `vfDimension`, including its
minus-infinity empty-set convention, rather than a comparison of dimension
definitions. Real parameter bases and their genuine smallness are explicit.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

/-- The explicit projection drops the RV index and leaves the singleton
empty RV tuple; it does not use an empty codomain or an empty function. -/
noncomputable def forgetRVCoordinatesMap (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n 0) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n 0
  let F (z : P.Index → M) : Q.Index → M := Sum.elim (z ∘ Sum.inl) Fin.elim0
  have hcode (c : P.domain) : mixedValues ((P.decode c).1, Fin.elim0) = F c.val := by
    have hc := mixedValues_decode c
    funext i
    cases i with
    | inl j => exact congrFun hc (.inl j)
    | inr j => exact j.elim0
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A (fun a => (a.1, Fin.elim0)) F
    (fun i => ?_) hdom ?_
  · cases i with
    | inl j => exact Set.DefinableFun.proj LRV
    | inr j => exact j.elim0
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode ⟨F c.val, hdom c⟩).trans (hcode c).symm

theorem forgetRVCoordinatesMap_mem (A : DefSet (rawMixedSpace (M := M) n r) S)
    (a : Fin n → VF M) :
    (a, Fin.elim0) ∈ (forgetRVCoordinatesMap A).image.carrier ↔
      ∃ t : Fin r → RVInfinity M, (a, t) ∈ A.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    have he : p.val.1 = a := congrArg Prod.fst hp
    exact ⟨p.val.2, he ▸ p.property⟩
  · rintro ⟨t, ht⟩
    exact ⟨⟨(a, t), ht⟩, rfl⟩

section Topological
variable [TopologicalSpace (VF M)]

theorem vfDimension_le_arity (A : Set (Mixed M n r)) :
    vfDimension A ≤ (n : WithBot ℕ) := by
  classical
  unfold vfDimension
  apply Finset.sup_le
  intro i _
  split_ifs
  · exact_mod_cast Nat.le_of_lt_succ i.isLt
  · exact bot_le

end Topological

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem forgetRV_full_dimension_iff
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDimension (forgetRVCoordinatesMap A).image.carrier = (n : WithBot ℕ) ↔
      vfDimension A.carrier = (n : WithBot ℕ) := by
  constructor
  · intro hdim
    obtain ⟨t₀, D, hD⟩ := (lemma_2_17 _).mp hdim
    have ht₀ : t₀ = Fin.elim0 := Subsingleton.elim _ _
    subst t₀
    obtain ⟨b, hb⟩ := exists_independent_of_contains_box hs hsmall
      (forgetRVCoordinatesMap A).image D.side
      (fun i => D.side_infinite (model_valuation_nontrivial hv) i) Fin.elim0
      (fun x hx => hD ((D.mem_carrier_iff x).mpr hx))
    obtain ⟨p, hp⟩ := b.property
    have he : p.val.1 = b.val.1 := congrArg Prod.fst hp
    have hpI : AlgebraicIndependent (vfParameterField S) p.val.1 := by
      rw [he]
      exact hb
    let T := S ∪ Set.range (rvValues p.val.2)
    have hpIT : AlgebraicIndependent (vfParameterField T) p.val.1 := by
      dsimp only [T]
      rw [vfParameterField_union_rv S _ (by rintro x ⟨i, rfl⟩; exact (p.val.2 i).property)]
      exact hpI
    have hnear := independent_definable_mem_nhds hv T (rawFixedRVFibre A p.val.2)
      (rawFixedRVFibre_sorted hc A p.val.2) p.val.1 hpIT
      ((mem_rawFixedRVFibre A p.val.2 p.val.1).mpr p.property)
    have hrow : {x : Fin n → VF M | vfValues x ∈ rawFixedRVFibre A p.val.2} =
        vfFibre A.carrier p.val.2 := Set.ext (mem_rawFixedRVFibre A p.val.2)
    rw [hrow] at hnear
    exact (vfDimension_eq_full_iff A.carrier).mpr
      ⟨p.val.2, p.val.1, mem_interior_iff_mem_nhds.mpr hnear⟩
  · intro hdim
    obtain ⟨t, a, ha⟩ := (vfDimension_eq_full_iff A.carrier).mp hdim
    have hsub : vfFibre A.carrier t ⊆
        vfFibre (forgetRVCoordinatesMap A).image.carrier Fin.elim0 := by
      intro x hx
      exact (forgetRVCoordinatesMap_mem A x).mpr ⟨t, hx⟩
    exact (vfDimension_eq_full_iff _).mpr
      ⟨Fin.elim0, a, interior_mono hsub ha⟩

theorem forgetRV_dimension_lt_iff
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDimension (forgetRVCoordinatesMap A).image.carrier < (n : WithBot ℕ) ↔
      vfDimension A.carrier < (n : WithBot ℕ) := by
  have he := forgetRV_full_dimension_iff hc hs hsmall hv A
  constructor
  · intro h
    exact lt_of_le_of_ne (vfDimension_le_arity A.carrier) (fun hA => h.ne (he.mpr hA))
  · intro h
    exact lt_of_le_of_ne (vfDimension_le_arity (forgetRVCoordinatesMap A).image.carrier)
      (fun hA => h.ne (he.mp hA))

/-- The author's RV-indexed union principle, in the manuscript's own
dimension and with the approved empty-set convention. Each fibre is viewed
in VF^n with the singleton empty RV tuple. No positive-arity restriction is
needed for this statement. -/
theorem rv_indexed_union_vfDimension_lt
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hfibres : ∀ t : Fin r → RVInfinity M,
      vfDimension ((vfFibre A.carrier t) ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M))) <
        (n : WithBot ℕ)) :
    vfDimension (forgetRVCoordinatesMap A).image.carrier < (n : WithBot ℕ) := by
  apply (forgetRV_dimension_lt_iff hc hs hsmall hv A).mpr
  apply lt_of_le_of_ne (vfDimension_le_arity A.carrier)
  intro he
  obtain ⟨t, ht⟩ := (vfDimension_eq_full_iff A.carrier).mp he
  have hrow : vfDimension
      ((vfFibre A.carrier t) ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M))) =
      (n : WithBot ℕ) := by
    apply (vfDimension_eq_full_iff _).mpr
    refine ⟨Fin.elim0, ?_⟩
    have hset : vfFibre
        ((vfFibre A.carrier t) ×ˢ (Set.univ : Set (Fin 0 → RVInfinity M))) Fin.elim0 =
        vfFibre A.carrier t := by
      ext x
      exact and_iff_left (Set.mem_univ _)
    rw [hset]
    exact ht
  exact (hfibres t).ne hrow

end DiamondIntegral.Section2
