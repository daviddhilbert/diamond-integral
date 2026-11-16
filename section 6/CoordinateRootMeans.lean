import «section 6».FiniteCoordinateObstacles

/-! The complete original-base finite-family graph and actual mean
map of a coordinate-root family, with its explicit uniform cardinal
bound. Both VF parameters and existing RV labels remain in the graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem finiteIndexMean_definable {ι : Type} [Fintype ι] (h00 : M ⊨ Axioms.ACVF00)
    (F : (ι → M) → Finset (VF M))
    (hF : S.Definable LRV {z : ι ⊕ Fin 1 → M | ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)})
    (N : ℕ) (hN : ∀ z, (F z).card ≤ N) :
    S.DefinableFun LRV (fun z => (Barycentre.mean (F z)).val) := by
  let e := Fintype.equivFin ι
  let H (z : Fin (Fintype.card ι) → M) := F (z ∘ e)
  have hH : RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation H) :=
    hF.preimage_comp (Sum.map e id)
  have hf := Barycentre.mean_definable h00 S H hH N (fun z => hN (z ∘ e))
  have hh := hf.comp (show S.DefinableMap LRV (fun z : ι → M => z ∘ e.symm) from
    fun _ => Set.DefinableFun.proj LRV)
  simpa only [H,Function.comp_assoc,e.symm_comp_self,Function.comp_id] using hh

def coordinateRootGraphIndex (n r : ℕ) : Fin (n+1) ⊕ Fin r → (Fin n ⊕ Fin r) ⊕ Fin 1 :=
  Sum.elim (Fin.lastCases (.inr 0) (fun j => .inl (.inl j))) (fun j => .inl (.inr j))

namespace CoordinateRootFamily

variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def rawFamily (R : CoordinateRootFamily A) (z : Fin n ⊕ Fin r → M) : Finset (VF M) :=
  if hz : z ∈ (rawMixedSpace (M := M) n r).domain then
    R.fibre ((rawMixedSpace n r).decode ⟨z,hz⟩).1 ((rawMixedSpace n r).decode ⟨z,hz⟩).2 else ∅

theorem rawFamily_values (R : CoordinateRootFamily A) (p : Mixed M n r) :
    R.rawFamily (mixedValues p) = R.fibre p.1 p.2 := by
  rw [rawFamily,dite_eq_left (mixedValues_mem_domain p),decode_mixedValues]

theorem rawFamily_definable (R : CoordinateRootFamily A) :
    S.Definable LRV {z : (Fin n ⊕ Fin r) ⊕ Fin 1 → M |
      ∃ x ∈ R.rawFamily (z ∘ Sum.inl), x.val = z (.inr 0)} := by
  have h := ((mixed_definable_iff_values_image S _).mp R.roots.definable).preimage_comp
    (coordinateRootGraphIndex n r)
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,hx,hxz⟩
    by_cases hz : z ∘ Sum.inl ∈ (rawMixedSpace (M := M) n r).domain
    · let p := (rawMixedSpace (M := M) n r).decode ⟨z ∘ Sum.inl,hz⟩
      have hp : mixedValues p = z ∘ Sum.inl := mixedValues_decode _
      have hx' : x ∈ R.fibre p.1 p.2 := by
        simpa only [rawFamily,dite_eq_left hz,p] using hx
      refine ⟨(Fin.snoc p.1 x,p.2),(R.mem_fibre _ _ _).mp hx',?_⟩
      funext i
      cases i with
      | inl i =>
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [mixedValues,vfValues,Sum.elim_inl,Fin.snoc_last,Function.comp_apply,
            coordinateRootGraphIndex,Fin.lastCases_last] using hxz
        · simpa only [mixedValues,vfValues,Sum.elim_inl,Fin.snoc_castSucc,Function.comp_apply,
            coordinateRootGraphIndex,Fin.lastCases_castSucc] using congrFun hp (.inl j)
      | inr i =>
        simpa only [mixedValues,rvValues,Sum.elim_inr,Function.comp_apply,coordinateRootGraphIndex]
          using congrFun hp (.inr i)
    · have he : R.rawFamily (z ∘ Sum.inl) = ∅ := dif_neg hz
      exact (Finset.notMem_empty _ (he ▸ hx)).elim
  · rintro ⟨p,hp,hpz⟩
    have hLower : mixedValues (Fin.init p.1,p.2) = z ∘ Sum.inl := by
      funext i
      cases i with
      | inl i =>
        have hh := congrFun hpz (.inl i.castSucc)
        simpa only [mixedValues,vfValues,Sum.elim_inl,Function.comp_apply,coordinateRootGraphIndex,
          Fin.lastCases_castSucc,Fin.init] using hh
      | inr i =>
        have hh := congrFun hpz (.inr i)
        simpa only [mixedValues,rvValues,Sum.elim_inr,Function.comp_apply,coordinateRootGraphIndex] using hh
    refine ⟨p.1 (Fin.last n),?_,?_⟩
    · rw [← hLower,rawFamily_values,mem_fibre,Fin.snoc_init_self]
      exact hp
    · have hh := congrFun hpz (.inl (Fin.last n))
      simpa only [mixedValues,vfValues,Sum.elim_inl,Function.comp_apply,coordinateRootGraphIndex,
        Fin.lastCases_last] using hh

theorem rawFamily_bound (R : CoordinateRootFamily A) (N : ℕ) (hN : R.Bound N) :
    ∀ z, (R.rawFamily z).card ≤ N := by
  intro z
  by_cases hz : z ∈ (rawMixedSpace (M := M) n r).domain
  · rw [rawFamily,dite_eq_left hz]
    exact hN _ _
  · rw [rawFamily,dite_eq_right hz,Finset.card_empty]
    exact Nat.zero_le _

def meanMap (R : CoordinateRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (N : ℕ) (hN : R.Bound N) (C : DefSet (rawMixedSpace (M := M) n r) S) :
    Map C (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let F (p : Mixed M n r) : Fin 1 → VF M := fun _ => Barycentre.mean (R.fibre p.1 p.2)
  let codes (z : Fin n ⊕ Fin r → M) : Fin 1 → M := fun _ => (Barycentre.mean (R.rawFamily z)).val
  have hm := finiteIndexMean_definable h00 R.rawFamily R.rawFamily_definable N (R.rawFamily_bound N hN)
  have hd : S.DefinableMap LRV codes := fun _ => hm
  have hdom (z : (rawMixedSpace (M := M) n r).domain) : codes z.val ∈ (rawVFSpace 1).domain :=
    ⟨fun _ => Barycentre.mean (R.rawFamily z.val),rfl⟩
  refine Map.ofCodes C F codes hd hdom ?_
  intro z
  apply vfValues_injective
  refine (vfValues_decode _).trans ?_
  funext i
  change (Barycentre.mean (R.rawFamily z.val)).val = (Barycentre.mean (R.fibre _ _)).val
  rw [← mixedValues_decode z,rawFamily_values]

theorem meanMap_value (R : CoordinateRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (N : ℕ) (hN : R.Bound N) (C : DefSet (rawMixedSpace (M := M) n r) S) (p : C) :
    (R.meanMap h00 N hN C p).val 0 = Barycentre.mean (R.fibre p.val.1 p.val.2) := rfl

end CoordinateRootFamily
end DiamondIntegral.Section6
