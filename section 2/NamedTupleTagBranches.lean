import «section 2».NamedTagBranches

/-! Arbitrary finite source arity for full tagged branch graphs. The
imaginary disc tuple and the RV tag are retained without choosing centres. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem named_tuple_tag_branch_graph_definable (B : ParameterBase M)
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (A : Set (Fin n → M))
    (hA : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) A)
    (F : Set ((Fin n → M) × M))
    (hF : GammaParameters.DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F}) (t : RVInfinity M) (g : (Fin n → M) → M)
    (hg : ∀ x ∈ A, ∀ y, ((x,y) ∈ F ∧ iRv y = t.val) ↔ g x = y) :
    DefinableOverFiniteDiscNames (adjoinRV B t) closed a δ (fun _ : Fin (n+1) => .vf)
      (vfFunctionGraph A g) := by
  let U : Set (Fin n → M) := GammaParameters.sortedUniverse (fun _ => .vf)
  have hU : GammaParameters.DefinableOverBase B (fun _ : Fin n => .vf) U :=
    GammaParameters.real_definableOverBase B _ _ (GammaParameters.sortedUniverse_definable B.real _)
  have hT := vfTagBranch_definable B U F hU hF t
  have hTd := definableOverFiniteDiscNames_of_ground (adjoinRV B t) closed a δ
    (fun _ : Fin (n+1) => .vf) _ hT
  have hAp := (hA.mono (show B.real ⊆ (adjoinRV B t).real from Set.subset_insert _ _)
    (Set.Subset.refl _)).preimage_real (fun _ : Fin (n+1) => .vf) Fin.castSucc
  convert hAp.inter hTd using 1
  ext z
  change (Fin.init z ∈ A ∧ g (Fin.init z) = z (Fin.last n)) ↔
    ((Fin.init z ∈ A ∧ z ∈ GammaParameters.sortedUniverse (fun _ => .vf)) ∧
      (Fin.init z,z (Fin.last n)) ∈ vfTagBranch U F t)
  constructor
  · rintro ⟨hzA,hzg⟩
    have hf := (hg _ hzA _).mpr hzg
    have hs := hF.proper z hf.1
    exact ⟨⟨hzA,hs⟩,fun j => hs j.castSucc,hf⟩
  · rintro ⟨⟨hzA,_⟩,_,hf,ht⟩
    exact ⟨hzA,(hg _ hzA _).mp ⟨hf,ht⟩⟩

end DiamondIntegral.Section2
