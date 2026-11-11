import «section 2».RVMapPadding

/-! Products of actual RV finite maps. Input and output coordinates are
concatenated, retaining zero input tags and the original parameter base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvTupleProduct {m n : ℕ} (U : Set (Fin m → RVInfinity M)) (V : Set (Fin n → RVInfinity M)) :
    Set (Fin (m+n) → RVInfinity M) :=
  {x | x ∘ Fin.castAdd n ∈ U ∧ x ∘ Fin.natAdd m ∈ V}

theorem RVHasFiniteMap.product (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {m n k l : ℕ} {U : Set (Fin m → RVInfinity M)} {V : Set (Fin n → RVInfinity M)}
    (hU : RVHasFiniteMap S U k) (hV : RVHasFiniteMap S V l) :
    RVHasFiniteMap S (rvTupleProduct U V) (k+l) := by
  obtain ⟨fU,hUf,hUg⟩ := hU
  obtain ⟨fV,hVf,hVg⟩ := hV
  let pU (x : rvTupleProduct U V) : U := ⟨x.val ∘ Fin.castAdd n,x.property.1⟩
  let pV (x : rvTupleProduct U V) : V := ⟨x.val ∘ Fin.natAdd m,x.property.2⟩
  let g (x : rvTupleProduct U V) := Fin.append (fU (pU x)) (fV (pV x))
  have hinj : Function.Injective (fun x : rvTupleProduct U V => (pU x,pV x)) := by
    intro x y he
    apply Subtype.ext
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact congrFun (congrArg (fun p : U × V => p.1.val) he) i
    · exact congrFun (congrArg (fun p : U × V => p.2.val) he) i
  refine ⟨g,?_,?_⟩
  · intro t
    apply (((hUf (t ∘ Fin.castAdd l)).prod (hVf (t ∘ Fin.natAdd k))).preimage hinj.injOn).subset
    intro x hx
    constructor
    · funext i
      have h := congrFun hx (Fin.castAdd l i)
      simpa only [g,Fin.append_left,Function.comp_apply] using h
    · funext i
      have h := congrFun hx (Fin.natAdd k i)
      simpa only [g,Fin.append_right,Function.comp_apply] using h
  · let idxU : Fin (m+k) → Fin ((m+n)+(k+l)) := fun j =>
      Sum.elim (fun i => finSumFinEquiv (.inl (Fin.castAdd n i)))
        (fun i => finSumFinEquiv (.inr (Fin.castAdd l i)))
        ((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).symm j)
    let idxV : Fin (n+l) → Fin ((m+n)+(k+l)) := fun j =>
      Sum.elim (fun i => finSumFinEquiv (.inl (Fin.natAdd m i)))
        (fun i => finSumFinEquiv (.inr (Fin.natAdd k i)))
        ((finSumFinEquiv : Fin n ⊕ Fin l ≃ Fin (n+l)).symm j)
    have hinputU (z : Fin ((m+n)+(k+l)) → M) :
        (z ∘ idxU) ∘ finSumFinEquiv ∘ Sum.inl =
          (z ∘ finSumFinEquiv ∘ Sum.inl) ∘ Fin.castAdd n := by
      funext i
      simp only [Function.comp_apply,idxU,Equiv.symm_apply_apply,Sum.elim_inl]
    have houtputU (z : Fin ((m+n)+(k+l)) → M) :
        (z ∘ idxU) ∘ finSumFinEquiv ∘ Sum.inr =
          (z ∘ finSumFinEquiv ∘ Sum.inr) ∘ Fin.castAdd l := by
      funext i
      simp only [Function.comp_apply,idxU,Equiv.symm_apply_apply,Sum.elim_inr]
    have hinputV (z : Fin ((m+n)+(k+l)) → M) :
        (z ∘ idxV) ∘ finSumFinEquiv ∘ Sum.inl =
          (z ∘ finSumFinEquiv ∘ Sum.inl) ∘ Fin.natAdd m := by
      funext i
      simp only [Function.comp_apply,idxV,Equiv.symm_apply_apply,Sum.elim_inl]
    have houtputV (z : Fin ((m+n)+(k+l)) → M) :
        (z ∘ idxV) ∘ finSumFinEquiv ∘ Sum.inr =
          (z ∘ finSumFinEquiv ∘ Sum.inr) ∘ Fin.natAdd k := by
      funext i
      simp only [Function.comp_apply,idxV,Equiv.symm_apply_apply,Sum.elim_inr]
    have he : rvMapGraph (rvTupleProduct U V) g =
        (fun z => z ∘ idxU) ⁻¹' rvMapGraph U fU ∩ (fun z => z ∘ idxV) ⁻¹' rvMapGraph V fV := by
      ext z
      constructor
      · rintro ⟨x,hx,hy⟩
        refine ⟨⟨pU x,?_,?_⟩,⟨pV x,?_,?_⟩⟩
        · rw [hinputU]
          exact congrArg (fun w => w ∘ Fin.castAdd n) hx
        · rw [houtputU]
          funext i
          have h := congrFun hy (Fin.castAdd l i)
          simpa only [g,rvTargetValues,Fin.append_left,Function.comp_apply] using h
        · rw [hinputV]
          exact congrArg (fun w => w ∘ Fin.natAdd m) hx
        · rw [houtputV]
          funext i
          have h := congrFun hy (Fin.natAdd k i)
          simpa only [g,rvTargetValues,Fin.append_right,Function.comp_apply] using h
      · rintro ⟨⟨u,hxU,hyU⟩,⟨v,hxV,hyV⟩⟩
        rw [hinputU] at hxU
        rw [houtputU] at hyU
        rw [hinputV] at hxV
        rw [houtputV] at hyV
        let x : rvTupleProduct U V := ⟨Fin.append u.val v.val,by
          constructor
          · convert u.property using 1
            funext i
            exact Fin.append_left _ _ i
          · convert v.property using 1
            funext i
            exact Fin.append_right _ _ i⟩
        have hpu : pU x = u := Subtype.ext (funext (fun i => Fin.append_left _ _ i))
        have hpv : pV x = v := Subtype.ext (funext (fun i => Fin.append_right _ _ i))
        refine ⟨x,?_,?_⟩
        · funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simpa only [x,rvInputValues,Fin.append_left,Function.comp_apply] using congrFun hxU i
          · simpa only [x,rvInputValues,Fin.append_right,Function.comp_apply] using congrFun hxV i
        · change rvTargetValues (Fin.append (fU (pU x)) (fV (pV x))) = _
          rw [hpu,hpv]
          funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simpa only [rvTargetValues,Fin.append_left,Function.comp_apply] using congrFun hyU i
          · simpa only [rvTargetValues,Fin.append_right,Function.comp_apply] using congrFun hyV i
    apply raw_definableOver_sorted hc
    · rw [he]
      exact (hUg.raw_definable.preimage_comp idxU).inter (hVg.raw_definable.preimage_comp idxV)
    · exact rvMapGraph_sorted (rvTupleProduct U V) g

theorem rv_univ_definable (S : Set M) (m : ℕ) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' (Set.univ : Set (Fin m → RVInfinity M))) := by
  convert GammaParameters.sortedUniverse_definable S (fun _ : Fin m => .rv) using 1
  ext z
  constructor
  · rintro ⟨u,_,rfl⟩ i
    exact (u i).property
  · intro hz
    exact ⟨fun i => ⟨z i,hz i⟩,Set.mem_univ _,rfl⟩

end DiamondIntegral.Section2
