import «section 2».RVMapRestriction

/-! Finite-to-one RV maps on finite definable unions. Selecting the first
source piece keeps the target arity fixed; each new fibre is a finite union
of old finite fibres. No extra RV target tag is introduced. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m k : ℕ}

theorem rv_finite_map_empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    RVHasFiniteMap S (∅ : Set (Fin m → RVInfinity M)) k := by
  let f : (∅ : Set (Fin m → RVInfinity M)) → Fin k → RV M := fun u => u.property.elim
  refine ⟨f,?_,?_⟩
  · intro t
    apply Set.Subsingleton.finite
    intro u _ v _
    exact u.property.elim
  · have he : rvMapGraph ∅ f = ∅ := by
      ext z
      constructor
      · rintro ⟨u,_,_⟩
        exact u.property.elim
      · exact False.elim
    apply raw_definableOver_sorted hc
    · rw [he]
      exact Set.definable_empty
    · exact rvMapGraph_sorted ∅ f

theorem RVHasFiniteMap.union (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {U V : Set (Fin m → RVInfinity M)}
    (hU : RVHasFiniteMap S U k) (hV : RVHasFiniteMap S V k)
    (hUdef : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    RVHasFiniteMap S (U ∪ V) k := by
  classical
  obtain ⟨fU,hUf,hUg⟩ := hU
  obtain ⟨fV,hVf,hVg⟩ := hV
  let incU (u : U) : ↥(U ∪ V) := ⟨u.val,Or.inl u.property⟩
  let incV (v : V) : ↥(U ∪ V) := ⟨v.val,Or.inr v.property⟩
  let f (x : ↥(U ∪ V)) : Fin k → RV M :=
    if hx : x.val ∈ U then fU ⟨x.val,hx⟩ else fV ⟨x.val,x.property.resolve_left hx⟩
  refine ⟨f,?_,?_⟩
  · intro t
    apply (((hUf t).image incU).union ((hVf t).image incV)).subset
    intro x hx
    change f x = t at hx
    by_cases hxU : x.val ∈ U
    · left
      refine ⟨⟨x.val,hxU⟩,?_,Subtype.ext rfl⟩
      simpa only [Set.mem_ofPred_eq,f,dite_eq_left hxU] using hx
    · right
      refine ⟨⟨x.val,x.property.resolve_left hxU⟩,?_,Subtype.ext rfl⟩
      simpa only [Set.mem_ofPred_eq,f,dite_eq_right hxU] using hx
  · let C : Set (Fin (m+k) → M) :=
      {z | z ∘ finSumFinEquiv ∘ Sum.inl ∈ rvInputValues '' U}
    have he : rvMapGraph (U ∪ V) f = rvMapGraph U fU ∪ (rvMapGraph V fV \ C) := by
      ext z
      constructor
      · rintro ⟨x,hx,hy⟩
        by_cases hxU : x.val ∈ U
        · left
          refine ⟨⟨x.val,hxU⟩,hx,?_⟩
          simpa only [f,dite_eq_left hxU] using hy
        · right
          refine ⟨⟨⟨x.val,x.property.resolve_left hxU⟩,hx,?_⟩,?_⟩
          · simpa only [f,dite_eq_right hxU] using hy
          · rintro ⟨u,hu,huz⟩
            have huval : u = x.val := rvInputValues_injective (huz.trans hx.symm)
            exact hxU (huval ▸ hu)
      · rintro (⟨u,hx,hy⟩ | ⟨⟨v,hx,hy⟩,hno⟩)
        · let x : ↥(U ∪ V) := incU u
          have hf : f x = fU u := by simp only [f,x,incU,dite_eq_left u.property]
          refine ⟨x,hx,?_⟩
          rwa [hf]
        · let x : ↥(U ∪ V) := incV v
          have hxU : x.val ∉ U := fun h => hno ⟨v.val,h,hx⟩
          have hf : f x = fV v := by simp only [f,dite_eq_right hxU]; rfl
          refine ⟨x,hx,?_⟩
          rwa [hf]
    apply raw_definableOver_sorted hc
    · rw [he]
      exact hUg.raw_definable.union (hVg.raw_definable.sdiff
        (hUdef.raw_definable.preimage_comp (fun j => finSumFinEquiv (.inl j))))
    · exact rvMapGraph_sorted (U ∪ V) f

theorem rv_finite_map_finite_union (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (Q : Set (Set (Fin m → RVInfinity M))) (hQ : Q.Finite)
    (hMaps : ∀ V ∈ Q, RVHasFiniteMap S V k)
    (hDefs : ∀ V ∈ Q, DefinableOver S (fun _ => .rv) (rvInputValues '' V)) :
    RVHasFiniteMap S (⋃₀ Q) k := by
  classical
  revert hMaps hDefs
  induction Q, hQ using Set.Finite.induction_on with
  | empty =>
    intro _ _
    simpa only [Set.sUnion_empty] using (rv_finite_map_empty hc S (m := m) (k := k))
  | @insert V Q hnot hQ ih =>
    intro hMaps hDefs
    rw [Set.sUnion_insert]
    exact (hMaps V (Set.mem_insert V Q)).union hc
      (ih (fun W hW => hMaps W (Set.mem_insert_of_mem V hW))
        (fun W hW => hDefs W (Set.mem_insert_of_mem V hW)))
      (hDefs V (Set.mem_insert V Q))

end DiamondIntegral.Section2
