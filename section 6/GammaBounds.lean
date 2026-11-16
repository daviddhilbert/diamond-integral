import «section 6».TubularGammaGraphs

/-! The full Lemma 6.22. The source need not be invariant or closed.
Its uniform tubular neighborhood is definable, bounded and invariant;
the original Gamma function extends uniquely and definably to it. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Lemma 6.22 with exactly the source boundedness assumptions in the
manuscript, including arbitrary RV tags, arity zero and unnamed radius. -/
theorem lemma_6_22
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : Set (Mixed M n r)) (hA : (rawMixedSpace (M := M) n r).Definable S A)
    (hVF : VFBounded A) (hRV : RVSupportDoublyBounded A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f)) (γ : Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => γ) a b → f (a,u) = f (b,u)) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ f a ∧ f a ≤ δ := by
  let ρ : Gamma M := max 1 γ
  obtain ⟨t,ht,htρ⟩ := GammaParameters.EndpointLogic.codeValue_surjective ρ
  let T := S ∪ {t}
  have hST : S ⊆ T := Set.subset_union_left
  have hTs : Cardinal.mk T < κ := small_union_finite hκ.le S hsmall {t} (Set.finite_singleton t)
  have hρdef : T.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}} := by
    rw [← htρ]
    exact gamma_codeValue_named T t ht (Or.inr (Set.mem_singleton t))
  have hconstρ : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => ρ) a b → f (a,u) = f (b,u) :=
    fun u a ha b hb hab => hconst u a ha b hb (hab.of_larger_radius (fun _ => le_max_right _ _))
  let H := tubularHull ρ A
  let f' := tubularExtension ρ A f
  have hgraph : T.Definable LRV (mixedGammaGraph H f') := by
    rw [tubularExtension_graph ρ A f hconstρ]
    exact tubularGammaRelation_definable ρ hρdef A f (hf.mono hST)
  have hHdef : (rawMixedSpace (M := M) n r).Definable T H := by
    apply (mixedTuple_image_definable_iff H).mp
    rw [← mixedGammaGraph_domain_codes H f']
    exact hgraph.image_comp Sum.inl
  have hH : ProperInvariant T H :=
    (lemma_6_5 h00 hc hκ hs hv H hHdef (tubularHull_vfBounded ρ hVF) (tubularHull_rvBounded ρ hRV)).mpr
      (fun u => (tubularHull_invariant ρ A u).isClopen hv)
  obtain ⟨δ,hδ⟩ := locally_constant_gamma_bounded_named h00 hc linear hκ hs hv hTs
    (hΓ.mono hST (Set.empty_subset _)) hH f' hgraph ρ (le_max_left _ _) hρdef
    (tubularExtension_constant ρ A f hconstρ)
  refine ⟨δ,fun a ha => ?_⟩
  have he : f' a = f a := tubularExtension_agrees ρ A f hconstρ ha
  exact he ▸ hδ a (subset_tubularHull ρ A ha)

end DiamondIntegral.Section6
