import «section 2».RVMapUnions

/-! Padding an RV finite map with parameter-free unit coordinates. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvOne : RV M :=
  ⟨rv M (1 : VF M),fun h => one_ne_zero ((rv_eq_zero_iff (1 : VF M)).mp h)⟩

theorem rvOne_raw_definable (S : Set M) {α : Type} :
    S.DefinableFun LRV (fun _ : α → M => (rvOne (M := M)).val.val) := by
  have h1 : S.Definable₁ LRV {(1 : VF M).val} :=
    SpecialTransformations.DefinableConstants.function_symbol (L := LRV) (A := S)
      Fn.vfOne Fin.elim0 (fun i => i.elim0)
  have hr : S.Definable₁ LRV {(rv M (1 : VF M)).val} :=
    SpecialTransformations.DefinableConstants.function_symbol Fn.rvMap ![(1 : VF M).val]
      (by intro i; fin_cases i; exact h1)
  exact SpecialTransformations.DefinableConstants.constant hr

theorem RVHasFiniteMap.append_constants (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {m k : ℕ} {U : Set (Fin m → RVInfinity M)} (hU : RVHasFiniteMap S U k)
    (l : ℕ) : RVHasFiniteMap S U (k+l) := by
  obtain ⟨f,hfin,hG⟩ := hU
  let g (u : U) := Fin.append (f u) (fun _ : Fin l => rvOne (M := M))
  refine ⟨g,?_,?_⟩
  · intro t
    apply (hfin (t ∘ Fin.castAdd l)).subset
    intro u hu
    funext i
    have h := congrFun hu (Fin.castAdd l i)
    simpa only [g,Fin.append_left,Function.comp_apply] using h
  · let oldidx : Fin (m+k) → Fin (m+(k+l)) := fun j =>
      Sum.elim (fun i => finSumFinEquiv (.inl i))
        (fun i => finSumFinEquiv (.inr (Fin.castAdd l i)))
        ((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm j)
    have hinput (z : Fin (m+(k+l)) → M) :
        (z ∘ oldidx) ∘ finSumFinEquiv ∘ Sum.inl = z ∘ finSumFinEquiv ∘ Sum.inl := by
      funext i
      simp only [Function.comp_apply,oldidx,Equiv.symm_apply_apply,Sum.elim_inl]
    have houtput (z : Fin (m+(k+l)) → M) :
        (z ∘ oldidx) ∘ finSumFinEquiv ∘ Sum.inr =
          (z ∘ finSumFinEquiv ∘ Sum.inr) ∘ Fin.castAdd l := by
      funext i
      simp only [Function.comp_apply,oldidx,Equiv.symm_apply_apply,Sum.elim_inr]
    let C : Set (Fin (m+(k+l)) → M) :=
      {z | ∀ j : Fin l, z (finSumFinEquiv (.inr (Fin.natAdd k j))) = (rvOne (M := M)).val.val}
    have hC : S.Definable LRV C := by
      convert Set.definable_iInter_of_finite (fun j : Fin l =>
        (Set.DefinableFun.proj LRV (i := finSumFinEquiv (.inr (Fin.natAdd k j)))).ofPred_eq
          (rvOne_raw_definable S)) using 1
      ext z
      simp only [C,Set.mem_ofPred_eq,Set.mem_iInter]
    have he : rvMapGraph U g = (fun z => z ∘ oldidx) ⁻¹' rvMapGraph U f ∩ C := by
      ext z
      constructor
      · rintro ⟨u,hx,hy⟩
        refine ⟨⟨u,?_,?_⟩,?_⟩
        · rwa [hinput]
        · rw [houtput]
          funext i
          have h := congrFun hy (Fin.castAdd l i)
          simpa only [g,rvTargetValues,Fin.append_left,Function.comp_apply] using h
        · intro j
          have h := congrFun hy (Fin.natAdd k j)
          simpa only [g,rvTargetValues,Fin.append_right,Function.comp_apply] using h.symm
      · rintro ⟨⟨u,hx,hy⟩,hzC⟩
        rw [hinput] at hx
        rw [houtput] at hy
        refine ⟨u,hx,?_⟩
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · have h := congrFun hy i
          simpa only [g,rvTargetValues,Fin.append_left,Function.comp_apply] using h
        · simpa only [g,rvTargetValues,Fin.append_right,Function.comp_apply] using (hzC i).symm
    apply raw_definableOver_sorted hc
    · rw [he]
      exact (hG.raw_definable.preimage_comp oldidx).inter hC
    · exact rvMapGraph_sorted U g

end DiamondIntegral.Section2
