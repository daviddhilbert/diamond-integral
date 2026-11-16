import «section 6».GammaLevelGraphs

/-! Corollary 6.23. Invariant Gamma level fibers acquire one common named
local-constancy radius. This is derived from the full equality relation
and the mixed partition bound, without using preparation existence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem firstVFBlock_append (a b : Fin n → VF M) (u : Fin r → RVInfinity M) :
    firstVFBlock (Fin.append a b,u) = (a,u) := by
  change (Fin.append a b ∘ Fin.castAdd n,u) = (a,u)
  refine Prod.ext ?_ rfl
  funext i
  exact Fin.append_left a b i

theorem secondVFBlock_append (a b : Fin n → VF M) (u : Fin r → RVInfinity M) :
    secondVFBlock (Fin.append a b,u) = (b,u) := by
  change (Fin.append a b ∘ Fin.natAdd n,u) = (b,u)
  refine Prod.ext ?_ rfl
  funext i
  exact Fin.append_right a b i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem gammaFunction_uniform_named_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f))
    (hlevels : ∀ u γ, IsOpen {a : Fin n → VF M | (a,u) ∈ A ∧ f (a,u) = γ}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ (1 : Gamma M) ≤ δ ∧
      ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
        Congruent (fun _ => δ) a b → f (a,u) = f (b,u) := by
  let R := gammaLevelRelation A f
  have hR : ProperInvariant S R :=
    (lemma_6_5 h00 hc hκ hs hv R (gammaLevelRelation_definable A f hf)
      (gammaLevelRelation_vfBounded hA.vfBounded f) (gammaLevelRelation_rvBounded hA.rvBounded f)).mpr
        (gammaLevelRelation_clopen_fibres A f (hA.clopen_fibres hv) hlevels)
  obtain ⟨δ,hδ,hδ0,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hR
  refine ⟨δ,hδ,hδ0,?_⟩
  intro u a ha b hb hab
  have hp : (Fin.append a a,u) ∈ R := by
    change firstVFBlock (Fin.append a a,u) ∈ A ∧ secondVFBlock (Fin.append a a,u) ∈ A ∧ _
    rw [firstVFBlock_append,secondVFBlock_append]
    exact ⟨ha,ha,rfl⟩
  have hclose : Congruent (fun _ => δ) (Fin.append a a) (Fin.append a b) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left,sub_self]
      exact gamma_lt_value_zero δ
    · simpa only [Fin.append_right] using hab i
  have hq := (hInv u _ _ hclose).mp hp
  change firstVFBlock (Fin.append a b,u) ∈ A ∧ secondVFBlock (Fin.append a b,u) ∈ A ∧ _ at hq
  rw [firstVFBlock_append,secondVFBlock_append] at hq
  exact hq.2.2

/-- Corollary 6.23. Only geometric invariance of each level is needed;
the full original-base Gamma graph is retained in the hypotheses. -/
theorem corollary_6_23
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f))
    (hlevels : ∀ γ, ProperInvariantGeometry {p | p ∈ A ∧ f p = γ}) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ f a ∧ f a ≤ δ := by
  obtain ⟨δ,hδ,hδ0,hconst⟩ := gammaFunction_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA f hf
    (fun u γ => ((hlevels γ).clopen_fibres hv u).isOpen)
  exact locally_constant_gamma_bounded_named h00 hc linear hκ hs hv hsmall hΓ hA f hf δ hδ0 hδ hconst

end DiamondIntegral.Section6
