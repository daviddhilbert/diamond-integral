import «section 2».RVDimensionBounds

/-! Finite RV maps under coordinate permutations, with the original
ground parameters and target arity retained. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvReindexed {m n : ℕ} (e : Fin m ≃ Fin n) (U : Set (Fin n → RVInfinity M)) :
    Set (Fin m → RVInfinity M) := {v | v ∘ e.symm ∈ U}

theorem RVHasFiniteMap.reindex (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {m n k : ℕ} {U : Set (Fin n → RVInfinity M)}
    (hU : RVHasFiniteMap S U k) (e : Fin m ≃ Fin n) :
    RVHasFiniteMap S (rvReindexed e U) k := by
  obtain ⟨f,hfin,hG⟩ := hU
  let inc (v : rvReindexed e U) : U := ⟨v.val ∘ e.symm,v.property⟩
  have hinj : Function.Injective inc := by
    intro u v h
    apply Subtype.ext
    funext i
    have he := congrFun (congrArg (fun w : U => w.val) h) (e i)
    simpa only [inc,Function.comp_apply,e.symm_apply_apply] using he
  let g : rvReindexed e U → Fin k → RV M := f ∘ inc
  refine ⟨g,fun t => (hfin t).preimage hinj.injOn,?_⟩
  let idx : Fin (n+k) → Fin (m+k) := fun j =>
    Sum.elim (fun i => finSumFinEquiv (.inl (e.symm i)))
      (fun i => finSumFinEquiv (.inr i))
      ((finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n+k)).symm j)
  have hinput (z : Fin (m+k) → M) :
      (z ∘ idx) ∘ finSumFinEquiv ∘ Sum.inl =
        (z ∘ finSumFinEquiv ∘ Sum.inl) ∘ e.symm := by
    funext i
    simp only [Function.comp_apply,idx,Equiv.symm_apply_apply,Sum.elim_inl]
  have houtput (z : Fin (m+k) → M) :
      (z ∘ idx) ∘ finSumFinEquiv ∘ Sum.inr = z ∘ finSumFinEquiv ∘ Sum.inr := by
    funext i
    simp only [Function.comp_apply,idx,Equiv.symm_apply_apply,Sum.elim_inr]
  have he : rvMapGraph (rvReindexed e U) g = (fun z => z ∘ idx) ⁻¹' rvMapGraph U f := by
    ext z
    constructor
    · rintro ⟨v,hx,hy⟩
      refine ⟨inc v,?_,?_⟩
      · rw [hinput]
        exact congrArg (fun w => w ∘ e.symm) hx
      · rwa [houtput]
    · rintro ⟨u,hx,hy⟩
      rw [hinput] at hx
      rw [houtput] at hy
      let v : rvReindexed e U := ⟨u.val ∘ e,by
        have hcomp : (u.val ∘ e) ∘ e.symm = u.val := by
          funext i
          simp only [Function.comp_apply,e.apply_symm_apply]
        change (u.val ∘ e) ∘ e.symm ∈ U
        rw [hcomp]
        exact u.property⟩
      have hv : inc v = u := Subtype.ext (funext (fun i => by
        simp only [inc,v,Function.comp_apply,e.apply_symm_apply]))
      refine ⟨v,?_,?_⟩
      · funext i
        have h := congrFun hx (e i)
        simpa only [rvInputValues,v,Function.comp_apply,e.symm_apply_apply] using h
      · change rvTargetValues (f (inc v)) = _
        rwa [hv]
  apply raw_definableOver_sorted hc
  · rw [he]
    exact hG.raw_definable.preimage_comp idx
  · exact rvMapGraph_sorted (rvReindexed e U) g

end DiamondIntegral.Section2
