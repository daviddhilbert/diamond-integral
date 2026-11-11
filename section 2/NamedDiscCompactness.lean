import «section 2».DiscNameProducts
import «section 2».FiniteChoice
import Section3.GammaFullDescent
import TypedModelMap

/-! Saturation with a fixed finite tuple of DC parameters. Chosen real
presentations are used only to obtain a finite subfamily of sets already
definable over the original DC names. They do not enter the selected sets. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def discCompactnessNames (S : Set M) {k : ℕ} (a : Fin k → VF M) (δ : Fin k → Gamma M) : Set M :=
  (S ∪ Set.range (vfValues a)) ∪ Set.range (GammaParameters.rawTuple (GammaParameters.representatives δ))

theorem DefinableOverFiniteDiscNames.raw_auxiliary {S : Set M} {k n : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    {sn : Fin n → SortTag} {U : Set (Fin n → M)}
    (hU : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ sn U) :
    (discCompactnessNames S a δ).Definable LRV U := by
  obtain ⟨R,rfl⟩ := hU
  let T := discCompactnessNames S a δ
  have h := R.definable_fibre a δ
  have hreal (c : M) (hc : c ∈ S ∪ Set.range (vfValues a)) :
      ∃ σ, GammaParameters.DefinableClosureAtBase (⟨T,∅⟩ : ParameterBase M) σ c := by
    have hcT : c ∈ T := Or.inl hc
    rcases TypedModelMap.sort_cover (M := M) c with hv | hr
    · exact ⟨.vf, GammaParameters.real_definableAtBase ⟨T,∅⟩ .vf {c}
        (definableClosureAt_of_mem hcT hv)⟩
    · exact ⟨.rv, GammaParameters.real_definableAtBase ⟨T,∅⟩ .rv {c}
        (definableClosureAt_of_mem hcT hr)⟩
  have hgamma (γ : Gamma M) (hγ : γ ∈ (∅ : Set (Gamma M)) ∪ Set.range δ) :
      GammaParameters.GammaDefinableClosureAtBase (⟨T,∅⟩ : ParameterBase M) γ := by
    obtain ⟨j,rfl⟩ := hγ.resolve_left (fun h => h)
    have he := congrFun (GammaParameters.representatives_values δ) j
    exact he ▸ GammaParameters.gamma_value_of_named_code ⟨T,∅⟩
      (GammaParameters.representatives δ j) (Or.inr (Set.mem_range_self j))
  exact ((GammaParameters.base_empty_iff T sn _).mp
    (h.eliminate_definable_params hreal hgamma)).raw_definable

theorem finite_subcover_disc_names
    {κ : Cardinal} (hs : Saturated M κ) (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    {k n : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (A : Set (Fin n → M))
    (hA : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) A)
    (K : Set (Set (Fin n → M)))
    (hK : ∀ C ∈ K, DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) C)
    (hcover : ∀ x ∈ A, ∃ C ∈ K, x ∈ C) :
    ∃ K₀ ⊆ K, K₀.Finite ∧ ∀ x ∈ A, ∃ C ∈ K₀, x ∈ C := by
  have ht := small_union_range hκ _ (small_union_range hκ S hsmall (vfValues a))
    (GammaParameters.rawTuple (GammaParameters.representatives δ))
  obtain ⟨K₀,hfin,hsub,hcov⟩ := hs.definable_finite_subcover_tuple
    (discCompactnessNames S a δ) ht A hA.raw_auxiliary K
    (fun C hC => (hK C hC).raw_auxiliary) hcover
  exact ⟨K₀,hsub,hfin,hcov⟩

theorem DefinableOverFiniteDiscNames.sorted_finite_iInter
    {B : ParameterBase M} {k n : ℕ} {closed : Fin k → Bool}
    {a : Fin k → VF M} {δ : Fin k → Gamma M} {sn : Fin n → SortTag}
    {ι : Type} [Finite ι] (F : ι → Set (Fin n → M))
    (hF : ∀ i, DefinableOverFiniteDiscNames B closed a δ sn (F i)) :
    DefinableOverFiniteDiscNames B closed a δ sn
      {x | x ∈ GammaParameters.sortedUniverse sn ∧ ∀ i, x ∈ F i} := by
  classical
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  convert DefinableOverFiniteDiscNames.sorted_iInter (fun i => F (e.symm i))
    (fun i => hF (e.symm i)) using 1
  ext x
  exact and_congr Iff.rfl e.symm.surjective.forall

end DiamondIntegral.Section2
