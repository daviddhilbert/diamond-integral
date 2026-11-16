import «section 6».RVIndexedEventualRadii

/-! Fixing a finite real prefix leaves a full definable Gamma family
on its RV tail. The prefix is adjoined only for the fibrewise estimate;
its smallness and the existing Gamma names are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def prefixRVFibre (D : Set (Fin (n+m) → M)) (a : Fin n → M) : Set (Fin m → M) :=
  {u | Fin.append a u ∈ D}

theorem prefixRVFibre_definable (D : Set (Fin (n+m) → M)) (hD : S.Definable LRV D) (a : Fin n → M) :
    (S ∪ Set.range a).Definable LRV (prefixRVFibre D a) := by
  apply (hD.mono Set.subset_union_left).preimage_map
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using LRV.definableFun_const (M := M) (A := S ∪ Set.range a)
      (a := a j) (Fin m) (Or.inr (Set.mem_range_self j))
  · simpa only [Fin.append_right] using
      (Set.DefinableFun.proj (L := LRV) (A := S ∪ Set.range a) (i := j))

theorem prefixGammaFibre_definable
    (D : Set (Fin (n+m) → M)) (P : (Fin (n+m) → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P)) (a : Fin n → M) :
    (S ∪ Set.range a).Definable LRV
      (rawGammaFamilyGraph (prefixRVFibre D a) (fun u => P (Fin.append a u))) := by
  let F (z : Fin m ⊕ Fin 1 → M) : Fin (n+m) ⊕ Fin 1 → M :=
    Sum.elim (Fin.append a (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hF : (S ∪ Set.range a).DefinableMap LRV F := by
    rintro (i | i)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [F,Sum.elim_inl,Fin.append_left] using
          LRV.definableFun_const (M := M) (A := S ∪ Set.range a) (a := a j)
            (Fin m ⊕ Fin 1) (Or.inr (Set.mem_range_self j))
      · simpa only [F,Sum.elim_inl,Fin.append_right,Function.comp_apply] using
          (Set.DefinableFun.proj (L := LRV) (A := S ∪ Set.range a) (i := (Sum.inl j : Fin m ⊕ Fin 1)))
    · exact Set.DefinableFun.proj LRV
  exact (hP.mono Set.subset_union_left).preimage_map hF

theorem append_prefix_tail (x : Fin (n+m) → M) :
    Fin.append (x ∘ Fin.castAdd m) (x ∘ Fin.natAdd n)=x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left _ _ _
  · exact Fin.append_right _ _ _

end DiamondIntegral.Section6
