import «section 2».CitedDiscRVImages
import «section 2».RVBranches
import «section 2».DiscTupleIntersection

/-! Full graphs of unary RV-tagged branches over the original ground
parameters together with exactly the retained disc names and RV tag. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem named_tag_branch_graph_definable (B : ParameterBase M)
    {k : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (D : Set M)
    (hD : DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin 1 => .vf) {z | z 0 ∈ D})
    (F : Set ((Fin 1 → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin 2 => .vf)
      {z | (Fin.init z,z (Fin.last 1)) ∈ F}) (t : RVInfinity M) (g : M → M)
    (hg : ∀ x ∈ D, ∀ y, ((fun _ : Fin 1 => x,y) ∈ F ∧ iRv y = t.val) ↔ g x = y) :
    DefinableOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ : Fin 2 => .vf)
      (scalarVFGraph D g) := by
  let U : Set (Fin 1 → M) := GammaParameters.sortedUniverse (fun _ : Fin 1 => .vf)
  have hU : GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf) U :=
    GammaParameters.real_definableOverBase B _ _ (GammaParameters.sortedUniverse_definable B.real _)
  have hT := vfTagBranch_definable B U F hU hF t
  have hTd := definableOverFiniteDiscNames_of_ground (adjoinRV B t) closed a δ
    (fun _ : Fin 2 => .vf) _ hT
  have hDp := (hD.mono (show B.real ⊆ (adjoinRV B t).real from Set.subset_insert _ _)
    (Set.Subset.refl _)).preimage_real (fun _ : Fin 2 => .vf) Fin.castSucc
  convert hDp.inter hTd using 1
  ext z
  have heta : (fun _ : Fin 1 => z 0) = Fin.init z := by
    funext j
    fin_cases j
    rfl
  change (z 0 ∈ D ∧ z 1 = g (z 0)) ↔
    ((Fin.init z ∈ {z | z 0 ∈ D} ∧ z ∈ GammaParameters.sortedUniverse (fun _ => .vf)) ∧
      (Fin.init z,z (Fin.last 1)) ∈ vfTagBranch U F t)
  constructor
  · rintro ⟨hzD,hzg⟩
    have hf := (hg (z 0) hzD (z 1)).mpr hzg.symm
    rw [heta] at hf
    have hzf : z ∈ {z : Fin 2 → M | (Fin.init z,z (Fin.last 1)) ∈ F} := hf.1
    have hs := hF.proper z hzf
    exact ⟨⟨hzD,hs⟩,fun j => hs j.castSucc,hf⟩
  · rintro ⟨⟨hzD,_⟩,_,hf,ht⟩
    have hf' : ((fun _ : Fin 1 => z 0),z 1) ∈ F ∧ iRv (z 1) = t.val := by
      rw [heta]
      exact ⟨hf,ht⟩
    exact ⟨hzD,((hg (z 0) hzD (z 1)).mp hf').symm⟩

end DiamondIntegral.Section2
