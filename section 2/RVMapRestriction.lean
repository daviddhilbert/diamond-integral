import «section 2».RVArityBound

/-! Restriction and monotonicity for the manuscript's actual finite-map
definition of RV dimension, always over the same real ground base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m k : ℕ}

theorem RVHasFiniteMap.restrict (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {U V : Set (Fin m → RVInfinity M)} (hU : RVHasFiniteMap S U k)
    (hVU : V ⊆ U) (hV : DefinableOver S (fun _ => .rv) (rvInputValues '' V)) :
    RVHasFiniteMap S V k := by
  obtain ⟨f,hfin,hgraph⟩ := hU
  let inc (v : V) : U := ⟨v.val,hVU v.property⟩
  have hinj : Function.Injective inc := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun w : U => w.val) h
  let g : V → Fin k → RV M := f ∘ inc
  refine ⟨g,fun t => (hfin t).preimage hinj.injOn,?_⟩
  have he : rvMapGraph V g = rvMapGraph U f ∩
      {z | z ∘ finSumFinEquiv ∘ Sum.inl ∈ rvInputValues '' V} := by
    ext z
    constructor
    · rintro ⟨v,hx,hy⟩
      exact ⟨⟨inc v,hx,hy⟩,v.val,v.property,hx⟩
    · rintro ⟨⟨u,hx,hy⟩,v,hv,hvx⟩
      have huv : u.val = v := rvInputValues_injective (hx.trans hvx.symm)
      have hi : inc ⟨v,hv⟩ = u := Subtype.ext huv.symm
      refine ⟨⟨v,hv⟩,hvx,?_⟩
      change rvTargetValues (f (inc ⟨v,hv⟩)) = _
      rwa [hi]
  apply raw_definableOver_sorted hc
  · rw [he]
    exact hgraph.raw_definable.inter
      (hV.raw_definable.preimage_comp (fun j => finSumFinEquiv (.inl j)))
  · exact rvMapGraph_sorted V g

theorem rvDimension_le_of_finite_map {S : Set M} {U : Set (Fin m → RVInfinity M)}
    (hU : RVHasFiniteMap S U k) : rvDimension S U ≤ (k : WithBot ℕ) := by
  classical
  by_cases hne : U.Nonempty
  · simp only [rvDimension,ite_eq_left hne]
    exact_mod_cast Nat.sInf_le hU
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,rvDimension_empty]
    exact bot_le

theorem rvDimension_mono (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (U V : Set (Fin m → RVInfinity M)) (hVU : V ⊆ U)
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U))
    (hV : DefinableOver S (fun _ => .rv) (rvInputValues '' V)) :
    rvDimension S V ≤ rvDimension S U := by
  classical
  by_cases hne : V.Nonempty
  · have hUne : U.Nonempty := hne.mono hVU
    have hmin : RVHasFiniteMap S U (sInf {l | RVHasFiniteMap S U l}) := by
      change sInf {l | RVHasFiniteMap S U l} ∈ {l | RVHasFiniteMap S U l}
      exact Nat.sInf_mem ⟨m,rv_finite_map_to_arity hc S U hU⟩
    have hle := rvDimension_le_of_finite_map (hmin.restrict hc hVU hV)
    simpa only [rvDimension,ite_eq_left hne,ite_eq_left hUne] using hle
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,rvDimension_empty]
    exact bot_le

end DiamondIntegral.Section2
