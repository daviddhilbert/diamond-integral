import «section 2».MixedGammaFamilies
import «section 2».PartitionBoundedVF

/-! Fixing actual RV coordinates in the full mixed graph. Each VF fibre
is definable over the original base plus precisely those finitely many
real RV names, as required by the pure VF proof of 2.53. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem mixed_vf_fibre_definable (S : Set M) (A : Set (Mixed M n m))
    (hA : S.Definable LRV (mixedTuple '' A)) (t : Fin m → RVInfinity M) :
    (S ∪ Set.range (rvInputValues t)).Definable LRV (vfValues '' vfFibre A t) := by
  let T := S ∪ Set.range (rvInputValues t)
  let Φ (z : Fin n → M) := Fin.append z (rvInputValues t)
  have hΦ : T.DefinableMap LRV Φ := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Φ,Fin.append_left] using (Set.DefinableFun.proj LRV (i := i))
    · simpa only [Φ,Fin.append_right] using
        LRV.definableFun_const (M := M) (A := T) (a := rvInputValues t i) (Fin n) (Or.inr (Set.mem_range_self i) : rvInputValues t i ∈ T)
  convert (hA.mono (Set.subset_union_left : S ⊆ T)).preimage_map hΦ using 1
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨(a,t),ha,rfl⟩
  · rintro ⟨x,hx,hxz⟩
    obtain ⟨he,ht⟩ := (mixedTuple_eq_append_iff x t z).mp hxz
    exact ⟨x.1,by change (x.1,t) ∈ A; simpa only [← ht] using hx,he⟩

theorem mixedGammaGraph_fibre_definable (S : Set M) (A : Set (Mixed M n m))
    (p : Mixed M n m → Gamma M) (hp : S.Definable LRV (mixedGammaGraph A p))
    (t : Fin m → RVInfinity M) :
    (S ∪ Set.range (rvInputValues t)).Definable LRV
      (vfGammaGraph (vfFibre A t) (fun a => p (a,t))) := by
  let T := S ∪ Set.range (rvInputValues t)
  let W (z : Fin n ⊕ Fin 1 → M) : Fin (n+m) ⊕ Fin 1 → M :=
    Sum.elim (Fin.append (z ∘ Sum.inl) (rvInputValues t)) (z ∘ Sum.inr)
  have hW : T.DefinableMap LRV W := by
    rintro (j | j)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [W,Sum.elim_inl,Fin.append_left,Function.comp_apply] using
          (Set.DefinableFun.proj LRV (i := (Sum.inl i : Fin n ⊕ Fin 1)))
      · simpa only [W,Sum.elim_inl,Fin.append_right] using
          LRV.definableFun_const (M := M) (A := T) (a := rvInputValues t i) (Fin n ⊕ Fin 1) (Or.inr (Set.mem_range_self i) : rvInputValues t i ∈ T)
    · exact Set.DefinableFun.proj LRV
  convert (hp.mono (Set.subset_union_left : S ⊆ T)).preimage_map hW using 1
  ext z
  constructor
  · rintro ⟨hNZ,a,ha,he,hγ⟩
    refine ⟨hNZ,(a,t),ha,?_,hγ⟩
    exact (mixedTuple_eq_append_iff (a,t) t (z ∘ Sum.inl)).mpr ⟨he,rfl⟩
  · rintro ⟨hNZ,x,hx,he,hγ⟩
    obtain ⟨hz,ht⟩ := (mixedTuple_eq_append_iff x t (z ∘ Sum.inl)).mp he
    refine ⟨hNZ,x.1,?_,hz,?_⟩
    · change (x.1,t) ∈ A
      simpa only [← ht] using hx
    · change GammaParameters.codeValue (z (.inr 0)) = p x at hγ
      simpa only [← ht] using hγ

end DiamondIntegral.Section2
